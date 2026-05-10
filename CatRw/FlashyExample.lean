import CatRw.Basic
import Mathlib
import CatRw.Tag

open AlgebraicGeometry CategoryTheory Opposite

variable {R S : CommRingCat}

set_option linter.style.setOption false
set_option trace.CatRw false
set_option CatRw.trace_iso_expr true
set_option warn.sorry false

noncomputable def spec_prod_iso {R S : CommRingCat} : Spec (R ⨯ S) ≅ Spec R ⨿ Spec S := by
  change Scheme.Spec.obj (op (R ⨯ S)) ≅ Spec R ⨿ Spec S
  cat_rw [Limits.opProdIsoCoprod R S, Limits.PreservesColimitPair.iso Scheme.Spec ..]

noncomputable
example {R S : CommRingCat} : Scheme.Spec.obj ((op R) ⨿ (op S)) ≅ Spec R ⨿ Spec S := by
  cat_rw [Limits.PreservesColimitPair.iso Scheme.Spec ..]

noncomputable
example {A B : GrpCat} : (forget _).obj (A ⨯ B) ≅ (forget _).obj A ⨯ (forget _).obj B := by
  cat_rw [Limits.PreservesLimitPair.iso ..]

example {R S T : CommRingCat} (φ : R ≅ T) (F G : Scheme ⥤ Scheme) (ψ : F ≅ G) :
    IsReduced (F.obj (Spec (R ⨯ S))) := by
  cat_rw [spec_prod_iso, φ, ψ]
  sorry

variable {α β : Type} (h : α = β) (a : α) (b : β)
