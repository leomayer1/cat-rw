import CatRw.Basic
import Mathlib
import CatRw.Tag

open AlgebraicGeometry CategoryTheory Opposite

variable {R S : CommRingCat}

noncomputable def spec_prod_iso {R S : CommRingCat} : Spec (R ⨯ S) ≅ Spec R ⨿ Spec S := by
  change Scheme.Spec.obj (op (R ⨯ S)) ≅ Spec R ⨿ Spec S
  cat_rw [Limits.opProdIsoCoprod R S, Limits.PreservesColimitPair.iso Scheme.Spec ..]

noncomputable
example {R S : CommRingCat} : Scheme.Spec.obj ((op R) ⨿ (op S)) ≅ Spec R ⨿ Spec S := by
  cat_rw [Limits.PreservesColimitPair.iso Scheme.Spec ..]

#check Limits.PreservesLimitPair.iso

noncomputable
example {A B : GrpCat} : (forget _).obj (A ⨯ B) ≅ (forget _).obj A ⨯ (forget _).obj B := by
  cat_rw [Limits.PreservesLimitPair.iso ..]

example {R S T : CommRingCat} (φ : R ≅ T) (F G : Scheme ⥤ Scheme) (ψ : F ≅ G) :
    IsReduced (F.obj (Spec (R ⨯ S))) := by
  cat_rw [spec_prod_iso, φ, ψ]
  sorry

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
