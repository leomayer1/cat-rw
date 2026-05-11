import CatRw.BasicV2
import Mathlib
import CatRw.Tag

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

variable {R S : CommRingCat}

set_option linter.style.setOption false
set_option trace.CatRw true
set_option CatRw.trace_iso_expr true
set_option warn.sorry false

noncomputable def spec_prod_iso {R S : CommRingCat} : Spec (R ⨯ S) ≅ Spec R ⨿ Spec S := by
  change Scheme.Spec.obj (op (R ⨯ S)) ≅ Spec R ⨿ Spec S
  cat_rw [Limits.opProdIsoCoprod R S, ← Limits.PreservesColimitPair.iso Scheme.Spec (op R) (op S)]
  exact Iso.refl _


noncomputable
example {R S : CommRingCat} : Scheme.Spec.obj ((op R) ⨿ (op S)) ≅ Spec R ⨿ Spec S := by
  cat_rw [← Limits.PreservesColimitPair.iso Scheme.Spec]
  exact Iso.refl _


noncomputable
example {A B : GrpCat} : (forget _).obj (A ⨯ B) ≅ (forget _).obj A ⨯ (forget _).obj B := by
  cat_rw [Limits.PreservesLimitPair.iso]

section
open Limits
lemma isZero_prod {C : Type*} [Category* C] [HasBinaryProducts C] (X Y : C) (hX : IsZero X)
    (hY : IsZero Y) : IsZero (X ⨯ Y) := by
  haveI : IsIso (prod.fst : X ⨯ Y ⟶ X) :=
    (BinaryFan.isLimit_iff_isIso_fst hY.isTerminal
      (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd)).mp ⟨prodIsProd X Y⟩
  exact hX.of_iso (asIso (prod.fst : X ⨯ Y ⟶ X))
end

open Scheme.Modules

noncomputable
example {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (M N P : Z.Modules) (φ : M ≅ N)
    (hN : Limits.IsZero ((pullback g).obj N)) (hP : Limits.IsZero ((pullback g).obj P)) :
    Limits.IsZero ((pullback (f ≫ g)).obj (M ⨯ P)) := by
  cat_rw [φ, ← pullbackComp]
  dsimp
  cat_rw [Limits.PreservesLimitPair.iso, Limits.PreservesLimitPair.iso]
  apply isZero_prod
  · exact Functor.map_isZero _ hN
  exact Functor.map_isZero _ hP
