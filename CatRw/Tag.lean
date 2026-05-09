import CatRw.Basic
import Mathlib

open AlgebraicGeometry

variable {X Y : Scheme} (φ : X ≅ Y)

include φ

@[cat_rw]
lemma AlgebraicGeometry.IsReduced.iso_iff :
    IsReduced X ↔ IsReduced Y :=
  ⟨fun _ => isReduced_of_isOpenImmersion φ.inv, fun _ => isReduced_of_isOpenImmersion φ.hom⟩

example : IsReduced X := by
  -- cat_rw [φ] should make the goal ⊢ IsReduced Y
  cat_rw [φ]
  sorry

#check Spec

example {R S : CommRingCat} (φ : Spec R ≅ Spec S) : IsReduced (Spec R) := by
  cat_rw [φ]
  sorry

noncomputable
def iso_of_iso {R S : CommRingCat} (φ : R ≅ S) : Spec R ≅ Spec S := Scheme.Spec.mapIso φ.op.symm
