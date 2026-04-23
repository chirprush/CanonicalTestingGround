import Mathlib.Data.Nat.Prime.Defs

import Canonical

-- This file contains theorems that might be difficult to solve without any
-- help, but when given partial help (like hypotheses), one would expect
-- Canonical to solve it

#check Nat.prime_def

-- Perhaps more confusingly, the following doesn't work
-- https://github.com/chasenorman/CanonicalLean/issues/29
theorem dummy (p : ℕ) (hp : p.Prime) (h : ∃ r : ℕ, p = 2 ^ r + 1) :
  ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  sorry

theorem exercise_13_4_10
  (p : ℕ) (hp : p.Prime) (h : ∃ r : ℕ, p = 2 ^ r + 1) :
  ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  -- Canonical should find something similar to the following but doesn't
  -- exact Exists.intro (Classical.choose (dummy hp h)) (Exists.choose_spec (dummy hp h))
  canonical -simp [dummy]
  -- Note that running the following (without -simp) crashes Canonical
  -- canonical [dummy]

-- This is a slightly different example, but something weird is going on here.
-- Canonical produces a proof term that is incorrect!
theorem dummy2 (h : ∃ k : ℕ, 128 * k = 256) : ∃ k : ℕ, 256 * k = 512 := by
  sorry

theorem solve_using_dummy2 (h : ∃ k : ℕ, 128 * k = 256) : ∃ k : ℕ, 256 * k = 512 := by
  -- canonical -simp [dummy2]
  -- The above produces the following proof term which is incorrect.
  exact
    Exists.intro
      (Classical.choose
        (dummy2
          (Exists.intro
            (Classical.choice
                (Classical.indefiniteDescription._proof_1 (fun a ↦ 128 * a = 256)
                  (Exists.intro h.choose (Exists.choose_spec h)))).1
            (Exists.choose_spec (Exists.intro h.choose (Exists.choose_spec h))))))
      (Exists.choose_spec (dummy2 (Exists.intro h.choose (Exists.choose_spec h))))
  -- Note that there is definitely some redundancy to the above. The following
  -- proof term does actually work
  -- exact
  --   Exists.intro
  --     (Classical.choose
  --       (dummy2 h))
  --     (Exists.choose_spec (dummy2 (Exists.intro h.choose (Exists.choose_spec h))))


-- The following is perhaps a simplification of the exercise above, and it runs
-- into the same problem where Canonical outputs a proof term that doesn't typecheck
theorem simple_dummy (a : ℕ)
  (h0 : a * a = 1024) (h1 : ∃ b : ℕ, b * b = 36) :
  ∃ k : ℕ, k * k = 36864 := by
  sorry

theorem solve_using_simple_dummy (a : ℕ)
  (h0 : a * a = 1024) (h1 : ∃ b : ℕ, b * b = 36) :
  ∃ k : ℕ, k * k = 36864 := by
  -- canonical -simp [simple_dummy]
  sorry

-- More about the panic: interestingly, if you replace * with ^ in `h` and run
-- Canonical without -simp, then the crash occurs. Note, however, that Canonical
-- is completely fine with hp having ^ in it, so this is a little confusing.
theorem similar_dummy (p : ℕ) (hp : p ^ 2 = 1) (h : ∃ r : ℕ, p = 2 * r + 1) :
  ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  sorry

theorem solve_similar_dummy (p : ℕ) (hp : p ^ 2 = 1) (h : ∃ r : ℕ, p = 2 * r + 1) :
  ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 := by
  -- Once again, running
  -- canonical [similar_dummy]
  -- outputs an incorrect proof term (if you run with -simp, then Canonical
  -- doesn't find anything). I'm not quite sure what's going on here
  sorry

-- To illustrate what I mean about the ^ versus *, try changing h to
-- (h : ∃ r : ℕ, p = 2 ^ r + 1) in both theorems.
