import CatRw.Basic
import Mathlib

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme} (φ : X ≅ Y) {C : Type*} [Category* C]

set_option trace.CatRw true

include φ

@[cat_rw]
lemma AlgebraicGeometry.IsReduced.iso_iff :
    IsReduced X ↔ IsReduced Y :=
  ⟨fun _ => isReduced_of_isOpenImmersion φ.inv, fun _ => isReduced_of_isOpenImmersion φ.hom⟩

example : IsReduced X := by
  -- cat_rw [φ] should make the goal ⊢ IsReduced Y
  cat_rw [φ]
  sorry

@[cat_rw_iso]
noncomputable
def iso_of_iso {R S : CommRingCat} (φ : R ≅ S) : Spec R ≅ Spec S := Scheme.Spec.mapIso φ.op.symm

example {R S : CommRingCat} (φ : R ≅ S) : IsReduced (Spec R) := by
  -- cat_rw [φ] should make the goal ⊢ IsReduced (Spec S)
  cat_rw [φ]
  sorry

@[cat_rw_iso]
def TopCat.sheafToPresheaf_iso {X : TopCat} {F G : Sheaf C X} (φ : F ≅ G) :
    F.obj ≅ G.obj := (sheafToPresheaf _ C).mapIso φ

example {X : TopCat} {F G : TopCat.Sheaf C X} (φ : F ≅ G) : Limits.IsZero F.obj := by
  cat_rw [φ]
  sorry

#check X ⨯ Y

noncomputable
example {X Y Z : AddCommGrpCat} (φ : Y ≅ X) : X ⨯ Z ≅ Y ⨯ Z := by
  cat_rw [φ]

noncomputable
example {X Y Z : Scheme} (φ : Y ≅ X) : X ⨯ Z ≅ Y ⨯ Z := by
  cat_rw [φ]

noncomputable
example {X Y Z : Scheme} (φ : Y ≅ X) : X ⨯ Z ≅ Y ⨯ Z := by
  cat_rw [← φ]

noncomputable
example {X Y Z : Scheme} (φ : Y ≅ X) : X ⨿ Z ≅ Y ⨿ Z := by
  cat_rw [φ]

noncomputable
example {R S : CommRingCat} (φ : R ≅ S) : Limits.IsZero (Spec R ⨯ X) := by
  cat_rw [φ]
  sorry
