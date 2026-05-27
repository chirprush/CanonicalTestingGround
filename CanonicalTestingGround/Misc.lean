import Canonical
import Mathlib.Tactic
import Init.Data.Function

import Mathlib.Topology.Filter
import Mathlib.RingTheory.Ideal.Prime

open Function

theorem zero_has_no_successor (hn : ∃ n : Nat, Nat.succ n = 0) : false := by
  exact by simp only [reduceCtorEq] <;> simpa only [reduceCtorEq] using Exists.choose_spec hn

-- Of course I don't think you're supposed to put false (the bool) here,
-- but Canonical crashes on this
theorem no_bad_functions_crash (f : Int -> Int) (hf : ∀ a b : Int, a ≤ b → f a < f b) :
  false := by
  sorry
  -- canonical

theorem no_bad_functions (f : Int -> Int) (hf : ∀ a b : Int, a ≤ b → f a < f b) :
  False := by
  canonical +debug [Int, lt_self_iff_false, not_false_eq_true]
  -- Tactic proof looks like the following (0 or any arbitrary integer works)
  -- have h0 : f 0 < f 0 := hf 0 0 (by simp)
  -- absurd h0
  -- simp only [lt_self_iff_false, not_false_eq_true]

def Forth (f : Int → Int) :=
  ∀ a α b : Int, f a = α → a < b → (∃ β : Int, α ≤ β ∧ f b = β)

def Back (f : Int → Int) :=
  ∀ a α β : Int, f a = α → α ≤ β → (∃ b : Int, a < b ∧ f b = β)

theorem no_surjective_bounded_morphism (f : Int → Int) (hSurj : Surjective f) (hForth : Forth f) (hBack : Back f) :
  False := by
  canonical +debug [Forth, Back, Surjective]

-- theorem or_inside_forall (p : ℕ → Prop) (h : ∀ k : ℕ, (p k ∨ 1 = 0)) : ∀ k : ℕ, p k := by
--   canonical -simp [Or.inl, Or.inr]

#check Filter.isOpen_setOf_mem

theorem isOpen_setOf_mem {s : Set α} : IsOpen { l : Filter α | s ∈ l } :=
  Eq.subst (Filter.Iic_principal s) Filter.isOpen_Iic_principal

-- Interestingly, canonical doesn't find the proof term given above
-- In fact, something weird seems to be going on where if you fill in h2 in
-- refine using Filter.isOpen_Iic_principal, it says the motive has no options?
theorem canonical_isOpen_setOf_mem {s : Set α} : IsOpen { l : Filter α | s ∈ l } := by
  canonical +refine [Filter.Iic_principal, Filter.isOpen_Iic_principal, Eq.subst]
--  canonical [Filter.Iic_principal, Filter.isOpen_Iic_principal, Eq.subst]

theorem isPrime_iff [Semiring α] {I : Ideal α} : Ideal.IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

-- Hmmm maybe I should also supply Canonical with the definitions used in the
-- type? Actually, canonicalSimple seemed to get it using some other stuff taken
-- from the type, but this is definitely something to experiment with
theorem canonical_isPrime_iff [Semiring α] {I : Ideal α} : Ideal.IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  { mp := fun a ↦ ⟨fun a_1 ↦ a.1 a_1, fun {x y} a_1 ↦ a.2 a_1⟩,
    mpr := fun a ↦ { ne_top' := fun a_1 ↦ a.1 a_1, mem_or_mem' := fun {x y} a_1 ↦ a.2 a_1 } }

theorem bot_prime [Semiring α] [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime := Ideal.isPrime_bot

theorem canonical_bot_prime [Semiring α] [Nontrivial α] [NoZeroDivisors α] : (⊥ : Ideal α).IsPrime := by
  canonical [Ideal.isPrime_bot, Semiring, Nontrivial, NoZeroDivisors, Bot.bot]
