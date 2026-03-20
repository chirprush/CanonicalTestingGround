import Mathlib.Data.Nat.Prime.Defs
import Canonical

-- This file contains theorems that might be difficult to solve without any
-- help, but when given partial help (like hypotheses), one would expect
-- Canonical to solve it

#check Nat.prime_def

theorem two_is_prime : Nat.Prime 2 := by
  have h0 : ∀ (n : Nat), n ∣ 2 → n = 1 ∨ n = 2 := by sorry
  have h1 : 2 ≤ 2 := by sorry
  -- Perhaps I'm using this wrong but I really think that given the above
  -- hypotheses Canonical should be able to solve the goal
  canonical [Nat.prime_def]

-- Note that if we put h0 and h1 together like the following then Canonical does
-- know to use exact
theorem two_is_prime_help : Nat.Prime 2 := by
  have h : 2 ≤ 2 ∧ ∀ (n : Nat), n ∣ 2 → n = 1 ∨ n = 2 := by sorry
  exact by simp only [Nat.prime_def] <;> exact h

-- A similar sort of behavior is exhibited in the following Github issue:
-- https://github.com/chasenorman/CanonicalLean/issues/29
theorem dummy {p : ℕ} (hp : p.Prime) (h : ∃ r : ℕ, p = 2 ^ r + 1) :
  ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  sorry

theorem exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
    canonical [dummy]
