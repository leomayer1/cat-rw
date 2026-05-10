import CatRw.Basic
import Mathlib

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme} (φ : X ≅ Y) {C : Type*} [Category* C]

include φ

@[cat_rw]
lemma AlgebraicGeometry.IsReduced.iso_iff :
    IsReduced X ↔ IsReduced Y :=
  ⟨fun _ => isReduced_of_isOpenImmersion φ.inv, fun _ => isReduced_of_isOpenImmersion φ.hom⟩

example [IsReduced Y] : IsReduced X := by
  cat_rw [φ]
  infer_instance

@[cat_rw_iso]
noncomputable
def iso_of_iso {R S : CommRingCat} (φ : R ≅ S) : Spec R ≅ Spec S := Scheme.Spec.mapIso φ.op.symm

@[cat_rw_iso]
def TopCat.sheafToPresheaf_iso {X : TopCat} {F G : Sheaf C X} (φ : F ≅ G) :
    F.obj ≅ G.obj := (sheafToPresheaf _ C).mapIso φ

example {R S : CommRingCat} [IsReduced (Spec S)] (φ : R ≅ S) : IsReduced (Spec R) := by
  -- cat_rw [φ] should make the goal ⊢ IsReduced (Spec S)
  cat_rw [φ]
  infer_instance

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
