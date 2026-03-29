import Mathlib.Data.Nat.Prime.Defs
import Canonical

-- This file contains theorems that might be difficult to solve without any
-- help, but when given partial help (like hypotheses), one would expect
-- Canonical to solve it

#check Nat.prime_def

theorem two_is_prime : Nat.Prime 2 := by
  have h0 : ∀ (n : Nat), n ∣ 2 → n = 1 ∨ n = 2 := by sorry
  -- canonical [Nat.prime_def, And]
  exact by simp only [Nat.prime_def] <;> exact ⟨Nat.le.refl, fun a a_1 ↦ h0 a a_1⟩

-- Perhaps more confusingly, the following doesn't work
-- https://github.com/chasenorman/CanonicalLean/issues/29
theorem dummy {p : ℕ} (hp : p.Prime) (h : ∃ r : ℕ, p = 2 ^ r + 1) :
  ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  sorry

theorem exercise_13_4_10
    {p : ℕ} {hp : Nat.Prime p} (h : ∃ r : ℕ, p = 2 ^ r + 1) :
    ∃ (k : ℕ), p = 2 ^ (2 ^ k) + 1 := by
    canonical +debug [dummy]

-- Some of the noise can be extracted away from the above example to give
-- something a little more readable. The basic idea is that we give Canonical
-- something it cannot prove outright (cannot produce a proof of the below
-- because it's not really meant for this kind of computation), but give it a
-- helping theorem that is exactly what we wish to prove.
-- Canonical ends up not finding a solution
theorem dummy2 : ∃ k : Nat, 256 * k = 512 := by
  sorry

-- In the debug output, I see that the first line has `Destruct` mentioned;
-- maybe Canonical is destructing first without trying to prove it directly?
theorem solve_from_dummy2 : ∃ k : Nat, 256 * k = 512 := by
  -- This might be the case because when you uncomment the following line
  -- destruct
  -- It looks a little weird in VS Code, but it seems like the mangled goal
  -- matches with the `+debug` outputs goal? I'm not quite sure
  canonical +debug [dummy2]
