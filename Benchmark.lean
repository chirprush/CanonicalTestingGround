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

-- def canonicalSimple (type : Expr) (names : NameSet) : MetaM BenchResult := do
--   IO.setNumHeartbeats 0
--   let premises := names.toArray
--   let env ← getEnv
--   let startTime ← IO.monoMsNow
--   let structs ← premises.filterMapM Destruct.getStruct
--   let structs := structs ++ (premises.filter (isStructure env))
--   let premises ← premises.filterM fun name => do pure (← Destruct.getStruct name).isNone
--   let config := {} -- Do I really need this or can I just leave it empty?
--   let goal ← mkFreshExprMVar type
--   let (goal', reconstruct) ← Canonical.withArityUnfold config.monomorphize do
--     Canonical.preprocess goal.mvarId! config structs
--   let typ ← Canonical.withArityUnfold config.monomorphize do goal'.withContext do
--     Canonical.toCanonical (← goal'.getType) premises (structs.push ``Canonical.Pi) config
--   -- Run canonical on the current thread
--   -- Perhaps we can use tryCatchRuntimeEx or something to capture panics?
--   let result ← Canonical.canonical typ s!"{← IO.rand 0 999}" 3 config.count
--   let proofs ← Canonical.postprocess result goal' config reconstruct
--   let endTime ← IO.monoMsNow
--   -- I'm not sure if it's quite correct to say that this is a timeout since it
--   -- could also be the case that Canonical exhausts the entire search/fails
--   let some first := proofs[0]? | (pure .timeout)
--   return .pass (endTime - startTime) (← ppExpr first).pretty'

-- Taken from https://github.com/chasenorman/CanonicalLean/blob/master/Canonical/Tactic.lean
-- For some reason (I'll have to figure this out), there are still some
-- discrepancies with this and the actual tactic output
def canonicalSimple (type : Expr) (names : NameSet) : MetaM BenchResult := do
  IO.setNumHeartbeats 0
  let startTime ← IO.monoMsNow

  let consts := names.toArray
  let config : Canonical.Config := {}
  -- Potential difference from tactic in this line, but it's not obvious why
  -- this would be problematic
  let goalMVar ← mkFreshExprMVar type
  let goal := goalMVar.mvarId!

  let (premises, structs) ← Canonical.getPremises goal consts config

  let (processedGoal, reconstruct) ← Canonical.withArityUnfold config.monomorphize do
    Canonical.preprocess goal config structs

  let typ ← Canonical.withArityUnfold config.monomorphize do processedGoal.withContext do
    Canonical.toCanonical (← processedGoal.getType) premises (structs.push ``Canonical.Pi) config

  let timeout := 3
  let result ← Canonical.canonical typ s!"{← IO.rand 0 99}" timeout config.count

  let proofs ← Canonical.postprocess result goal config reconstruct
  let endTime ← IO.monoMsNow

  let some first := proofs[0]? | pure .timeout
  -- Check [here](https://github.com/leanprover/lean4/blob/7490891f406b711fbe901f1fc69824de1f318645/src/Lean/Meta/Tactic/TryThis.lean#L217) for formatting
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
  | .const name _ => if !Name.isInternal name then singleton name else NameSet.empty
    -- It's sometimes beneficial to add definitions it seems
    -- TODO: Ask Chase for a better mechanism to tell what's relevant or not.

    -- let c := (env.find? name).get!
    -- if c matches .thmInfo _ -- && !Name.isInternal name
    -- then singleton name
    -- else NameSet.empty
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

def saveBenchResult (br : TreeMap.Raw String (Array BenchEntry)) (key : String) (entry : BenchEntry) : TreeMap.Raw String (Array BenchEntry) :=
  let prevEntries := br.getD key #[]
  br.insert key (prevEntries.push entry)

def writeBenchResults (br : TreeMap.Raw String (Array BenchEntry)) : IO Unit := do
  -- Could also use compressed instead of pretty
  let serialized := (Json.obj $ br.map (fun _ entry => entry.toJson)).pretty
  IO.FS.writeFile "benchResults.json" serialized

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
    -- `Mathlib.RingTheory.Ideal.Prime
    -- `Mathlib.CategoryTheory.Abelian.Injective.Dimension
    `Mathlib.InformationTheory.Hamming,
    `Mathlib.CategoryTheory.Sigma.Basic
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

    IO.println s!"Running benchmark ({constants.size} total constants)"

    try
      let tasks : Array (Option (Task _)) ← constants.mapM (fun cname => do
        let prevResults := (← benchResults.get).getD (cname.toString) #[]
        if (prevResults.map (BenchEntry.version ·)).contains version then do
          IO.println s!"Benching {cname}"
          IO.println   "  -> skipped"
          return none

        let task ← IO.asTask $ ((do
          let value := (env.find? cname).get!.value! (allowOpaque := true)
          let type := (env.find? cname).get!.type
          -- It might be a good idea to add definitions into the premises because
          -- this greatly improves stuff it seems
          let dependencies := (getDependencies env value) ++ (getDependencies env type)
          IO.println s!"Benching {cname}"
          IO.println s!"  -> premises: {dependencies.toArray}"
          let result ← canonicalSimple type dependencies -- (dependencies.insert `Ideal.IsPrime)
          IO.println s!"Finished {cname}"
          match result with
          | .panic msg => IO.println s!"  -> panic (msg: {msg})"
          | .timeout => IO.println "  -> timeout"
          | .pass time proof => IO.println s!"  -> pass (time elapsed: {time})"

          benchResults.set $
            saveBenchResult (← benchResults.get) cname.toString
            {
              thmName := cname.toString,
              thmStatement := (← ppExpr type).pretty',
              result := result,
              version := version
            }
        ) : MetaM Unit).toIO (ctxCore := ctx) (sCore := s)

        return (some task)
      )

      let _ ← IO.mapTasks
        (fun _ => do writeBenchResults (← benchResults.get))
        tasks.reduceOption.toList
    finally
      -- This is kinda useless because it gets run before any of the threads run
      -- I should figure out proper panic handling, because it would be bad if
      -- benchmark progress was lost because of it (maybe we should write to the
      -- .json every N theorems for autosaving?)
      writeBenchResults (← benchResults.get)

-- Things to look into:
-- -> Specific benchmark targets (things with binders like integralsl,
--    derivatives, sums, etc.) <- this relies a lot on the relevant
--    theorems/definitions and needs some care
