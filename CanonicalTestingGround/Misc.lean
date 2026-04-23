import Canonical
import Mathlib.Tactic
import Init.Data.Function

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

theorem or_inside_forall (p : ℕ → Prop) (h : ∀ k : ℕ, (p k ∨ 1 = 0)) : ∀ k : ℕ, p k := by
  canonical -simp [Or.inl, Or.inr]
