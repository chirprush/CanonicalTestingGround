import Canonical
import Lean
import Std

open Lean Std Core Meta

inductive BenchResult
  | pass (timeElapsed : Nat) (proof : String)
  | timeout
  | panic (msg : String)
  deriving FromJson, ToJson, Inhabited

structure BenchEntry where
  thmName : String
  thmStatement : String
  version : String
  result : BenchResult
  deriving FromJson, ToJson, Inhabited

def canonicalSimple (type : Expr) (names : NameSet) : MetaM BenchResult := do
  IO.setNumHeartbeats 0
  let premises := names.toArray
  let env ← getEnv
  let startTime ← IO.monoMsNow
  let structs ← premises.filterMapM Destruct.getStruct
  let structs := structs ++ (premises.filter (isStructure env))
  let premises ← premises.filterM fun name => do pure (← Destruct.getStruct name).isNone
  let config := { count := 1 } -- Do I really need this or can I just leave it empty?
  let goal ← mkFreshExprMVar type
  let (goal', reconstruct) ← Canonical.withArityUnfold config.monomorphize do
    Canonical.preprocess goal.mvarId! config structs
  let typ ← Canonical.withArityUnfold config.monomorphize do goal'.withContext do
    Canonical.toCanonical (← goal'.getType) premises (structs.push ``Canonical.Pi) config
  -- Run canonical on the current thread
  -- Perhaps we can use tryCatchRuntimeEx or something to capture panics?
  let result ← Canonical.canonical typ s!"{← IO.rand 0 999}" 3 config.count
  let proofs ← Canonical.postprocess result goal' config reconstruct
  let endTime ← IO.monoMsNow
  -- I'm not sure if it's quite correct to say that this is a timeout since it
  -- could also be the case that Canonical exhausts the entire search/fails
  let some first := proofs[0]? | (pure .timeout)
  return .pass (endTime - startTime) (← ppExpr first).pretty'

-- Filters to remove non-theorems, internal theorems, and theorems that do not
-- match the modules that we are testing
def isValidConstant (env : Environment) (allowed : Array Name) (name : Name) (c : ConstantInfo) : Bool :=
  if not (c matches .thmInfo _) then false
  else if Name.isInternal name then false
  else Option.getD (dflt := false) do
    let idx ← env.getModuleIdxFor? name
    let moduleName ← env.header.moduleNames[idx]?
    pure $ Array.any allowed (fun allowedName => (allowedName.toString).isPrefixOf (moduleName.toString))

-- Could use Expr.getUsedConstants and filter maybe
partial def getDependencies (env : Environment) (e : Expr) : NameSet :=
  match e with
  | .const name _ =>
    let c := (env.find? name).get!
    if c matches .thmInfo _ -- && !Name.isInternal name
    then singleton name
    else NameSet.empty
  | .app _ _ =>
    let fn := e.getAppFn'
    let args := e.getAppArgs.toList
    let fnDeps := getDependencies env fn
    let argsDeps :=
      List.foldl (· ∪ ·) NameSet.empty <|
      List.map (getDependencies env ·) <|
      args
    fnDeps ∪ argsDeps
  | .lam _name _type body _info =>
    getDependencies env body
  | .forallE _name _type body _info =>
    getDependencies env body
  | .letE _name _type value body _nondep =>
    getDependencies env value ∪ getDependencies env body
  | .mdata _d e =>
    getDependencies env e
  | .proj _name _idx struct =>
    getDependencies env struct
  | _ => NameSet.empty

def readBenchResults (path : String) : IO (TreeMap.Raw String (Array BenchEntry)) := do
  let benchContents ← IO.FS.readFile path
  let jsonContents := match Json.parse benchContents with
  | Except.ok v => v
  | Except.error _ => Json.mkObj []
  match jsonContents.getObj? with
  | Except.ok t => pure $ t.map (fun (_ : String) (x : Json) => (FromJson.fromJson? x).toOption.get!)
  | _ => throw $ IO.userError "Ill-formed JSON for benchmark results"

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution

  let benchResults : IO.Ref (TreeMap.Raw String (Array BenchEntry)) ←
    (IO.mkRef (← readBenchResults "benchResults.json")).toIO

  let version ← match args with
  | ["-v", v] => pure v
  | _ => throw $ IO.userError "Please provide a version for benchmarking"

  let benching := #[
    -- `Mathlib.Topology.Filter
    -- `Mathlib.LinearAlgebra.Matrix.Ideal
    `Mathlib.RingTheory.Ideal.Prime
  ]


  let env ← importModules
    (loadExts := true)
    (benching.map (fun n => { module := n }) ++ #[ { module := `Canonical.Symbols }] )
    {}

  let ctx := { fileName := "", fileMap := default, maxHeartbeats := 50000000 }
  let s := { env }

  CoreM.toIO'
    (ctx := ctx)
    (s := s) do MetaM.run' do
    let constants := env.constants.fold (init := #[]) (fun acc name ci =>
      if isValidConstant env benching name ci then acc.push name else acc)
    -- let constants :=  #[`RingCon.matrix_strictMono_of_nonempty] -- #[`Ideal.isPrime_iff]

    let env := ← getEnv

    IO.println "Running benchmark!"

    constants.forM (fun cname => do
      let prevResults := (← benchResults.get).getD (cname.toString) #[]
      if (prevResults.map (·.version)).contains version then do
        IO.println s!"Benching {cname}"
        IO.println   "  -> skipped"
        return ()

      let _ ← IO.asTask $ (do
        let value := (env.find? cname).get!.value!
        let type := (env.find? cname).get!.type
        let dependencies := getDependencies env value
        -- It might be a good idea to add definitions into the premises because
        -- this greatly improves stuff it seems
        let result ← canonicalSimple type (dependencies.insert `Ideal.IsPrime)
        IO.println s!"Benching {cname}"
        IO.println s!"  -> type: {type}"
        -- IO.println s!"  -> proof: {value}"
        IO.println s!"  -> premises: {dependencies.toArray}"
        match result with
        | .panic msg => IO.println s!"  -> panic (msg: {msg})"
        | .timeout => IO.println "  -> timeout"
        | .pass time proof => IO.println s!"  -> pass (time elapsed: {time})"
      ).toIO (ctxCore := ctx) (sCore := s)


      -- TODO:
      -- -> Now that we've filtered the theorems correctly let's try and adapt
      --    runOnConst for our purposes (what's going on with the value stuff?
      --    are we extracting the dependencies and then running Canonical given
      --    on those dependencies? because I thought the theorem statement in of
      --    itself would be in the type field)
      -- -> I understand the above now a little bit better! We pass in the value
      --    (the proof) likely to get symbols from it (this is the main point I
      --    can't immediately see), but the way that we access the type is via
      --    inferType which just gives the same value back because the
      --    expressions typecheck already
      -- -> Figure out multithreading and how we want to do this
    )

-- I think my plan is going to be the following:
-- Fade the stuff in DataGeneration (trying to understand if it's even aligned
-- with what I'm trying to do is taking up time) and at least do what is the
-- natural solution for me:
-- -> Collect all theorem dependencies used in the proof (either recycle some
--    code from relevant or use a little bit of iterFast)
-- -> Feed these into Canonical as premises and sit back and let it do it's
--    thing lowkey
-- This actually works! Yippee! I'm not quite sure how to handle panics yet but
-- this will probably be apparent
