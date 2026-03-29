import Canonical
import Mathlib.Algebra.Group.Irreducible.Indecomposable
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Matrix.Ideal

#check isMulIndecomposable_id_univ

theorem canonical_isMulIndecomposable_id_univ
  {M : Type u_2} [Monoid M] [Subsingleton Mˣ] {x : M} (hx : x ≠ 1) :
  -- canonical [isUnit_iff_eq_one._simp_2, Irreducible.isUnit_or_isUnit]
  IsMulIndecomposable id Set.univ x ↔ Irreducible x := by
  destruct
  -- Getting a weird error about free variables here... maybe because of destruct?
  · canonical [Monoid, isUnit_iff_eq_one._simp_2, Irreducible.isUnit_or_isUnit]
  · sorry -- canonical [Irreducible.isUnit_or_isUnit]
  -- Should probably find something like the following proof from Mathlib,
  -- but it doesn't seem to. Not really sure what's going on
  -- ⟨fun h ↦ ⟨by simpa, by simpa using h⟩, fun h ↦ by simpa using h.isUnit_or_isUnit⟩

#check RingCon.matrix_strictMono_of_nonempty

theorem canonical_RingCon.matrix_strictMono_of_nonempty
  {R : Type u_1} (n : Type u_2) [NonUnitalNonAssocSemiring R] [Fintype n] [Nonempty n] :
  StrictMono (RingCon.matrix (R := R) n) := by
  canonical [RingCon.matrix_monotone, StrictMono, RingCon.matrix_injective, Monotone.strictMono_of_injective]
