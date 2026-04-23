import Mathlib.Data.Nat.Prime.Defs
import Canonical

theorem two_is_prime : Nat.Prime 2 := by
  have h0 : ∀ (n : Nat), n ∣ 2 → n = 1 ∨ n = 2 := by sorry
  -- canonical [Nat.prime_def, And]
  exact Nat.prime_def.2 ⟨Nat.le.refl, fun m a ↦ h0 m a⟩

theorem dummy : ∃ k : Nat, 256 * k = 512 := by
  sorry

theorem solve_from_dummy : ∃ k : Nat, 256 * k = 512 := by
  -- Perhaps Canonical should really find `exact dummy`?
  -- In fact, this motivates us to look at more convoluted examples of this
  -- instance to see if Canonical really can find simpler proofs
  -- canonical -simp [dummy]
  exact Exists.intro (Classical.choose dummy) (Exists.choose_spec dummy)
