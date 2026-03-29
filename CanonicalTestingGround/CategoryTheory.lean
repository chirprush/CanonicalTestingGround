import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Homotopy
import Canonical
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.Compactum

open CategoryTheory Limits Comma

#check CategoryTheory.Over.mono_homMk

theorem canonical_CategoryTheory.Over.mono_homMk
  {T : Type u_1} [Category.{v_1, u_1} T] {X : T} {U V : Over X}
  {f : U.left ⟶ V.left} [Mono f]
  (w : CategoryStruct.comp f V.hom = U.hom) :
  Mono (CategoryTheory.Over.homMk f w) := by
  canonical +debug [
    CategoryTheory.Over.forget_faithful,
    CategoryTheory.Over.forget,
    Functor.mono_of_mono_map
  ]
  -- Mathlib proof is essentially the following (I unraveled the assumption
  -- tactic in the last part with show_term):
  -- exact (CategoryTheory.Over.forget X).mono_of_mono_map (by (expose_names; exact inst_1))

#check compactumToCompHaus.essSurj

-- Lots of monomorphization errors again and some timeouts
-- (remove +debug for more info)
theorem canonical_compactumToCompHaus.essSurj : compactumToCompHaus.EssSurj := by
  canonical +debug [compactumToCompHaus.isoOfTopologicalSpace, Compactum.ofTopologicalSpace, CategoryTheory.Iso, Nonempty.intro, TopCat.carrier, compactumToCompHaus, True, TopCat, CompHaus, Compactum, CompHausLike.toTop, CategoryTheory.Functor.obj]

#check CategoryTheory.Limits.HasImageMap.transport

-- This seems to work! I think there's a lot of potential for Canonical in
-- category theory because many of the arguments rely mostly on chasing and
-- using the right objects in the right definitions

-- Actually, upon a new update, Canonical fails to find a proof
theorem canonical_HasImageMap.transport {C : Type u} [Category.{v, u} C] {f g : Arrow C} [HasImage f.hom]
  [HasImage g.hom] (sq : f ⟶ g) (F : MonoFactorisation f.hom) {F' : MonoFactorisation g.hom}
  (hF' : IsImage F') (map : F.I ⟶ F'.I)
  (map_ι : CategoryStruct.comp map F'.m = CategoryStruct.comp F.m sq.right) :
  HasImageMap sq := by
  sorry
  -- canonical [CategoryTheory.Limits.ImageMap.transport, CategoryTheory.Limits.HasImageMap.mk]
  -- exact HasImageMap.mk (ImageMap.transport sq F hF' map_ι)

#check CategoryTheory.Functor.mapHomotopyEquiv_inv

-- Lots of monomorphization failures (these seem to be warnings, but they could
-- be causing the unify failure later)
-- The line outputting these is [here](https://github.com/chasenorman/CanonicalLean/blob/80b1c39958f18845820bb1964bd372b0a2705b2f/Canonical/Monomorphize.lean#L166)
-- Also, Canonical fails to solve a universe constraint

-- When run without +debug, Canonical crashes
theorem canonical_CategoryTheory.Functor.mapHomotopyEquiv_inv
  {ι : Type u_1} {V : Type u} [Category.{v, u} V]
  [Preadditive V] {c : ComplexShape ι} {C D : HomologicalComplex V c} {W : Type u_2}
  [Category.{v_1, u_2} W] [Preadditive W]
  (F : Functor V W) [F.Additive] (h : HomotopyEquiv C D) :
  (F.mapHomotopyEquiv h).inv = (F.mapHomologicalComplex c).map h.inv := by
  canonical +debug [HomologicalComplex, HomologicalComplex.Hom, HomotopyEquiv.inv, Eq.refl, CategoryTheory.Functor.mapHomotopyEquiv, CategoryTheory.Functor.obj, CategoryTheory.Functor.mapHomologicalComplex]
