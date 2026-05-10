import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Tactic

open CategoryTheory Limits

variable {C : Type*} [Category C] [HasBinaryProducts C] [HasBinaryCoproducts C] [HasZeroObject C]
variable {D : Type*} [Category D] [HasBinaryProducts D] [HasBinaryCoproducts D] [HasZeroObject D]

set_option trace.CatRw true

/-- Deeply nested binary product and coproduct rewrite. -/
noncomputable
example (X Y Z W : C) (h : X ≅ Y) (k : Z ≅ W) :
    (X ⨯ Z) ⨿ (W ⨯ Y) ≅ (Y ⨯ W) ⨿ (Z ⨯ X) := by
  cat_rw [h, k]

/-- Nested functorial rewrite. -/
example (F G : C ⥤ D) (X Y : C) (η : F ≅ G) (e : X ≅ Y) :
    F.obj X ≅ G.obj Y := by
  cat_rw [η, e]

/-- Goal rewriting with `IsZero`. -/
example (X Y : C) (h : X ≅ Y) (hz : IsZero X) : IsZero Y := by
  have : IsZero X ↔ IsZero Y := by
    cat_rw [h]
    exact Iff.rfl
  exact this.mp hz

/-- Goal rewriting with `PreservesMonomorphisms`. -/
example (F G : C ⥤ D) (h : F ≅ G) (hm : F.PreservesMonomorphisms) : G.PreservesMonomorphisms := by
  have : F.PreservesMonomorphisms ↔ G.PreservesMonomorphisms := by
    cat_rw [h]
    exact Iff.rfl
  exact this.mp hm

/-- Multiple rule application in a single call. -/
example (X Y Z : C) (h1 : X ≅ Y) (h2 : Y ≅ Z) : X ≅ Z := by
  cat_rw [h1, h2]

/-- Rewriting with natural isomorphisms and app. -/
example (F G : C ⥤ D) (X : C) (η : F ≅ G) : F.obj X ≅ G.obj X := by
  cat_rw [η]

/-- Complex composition of products and symmetry. -/
noncomputable
example (X Y Z : C) : (X ⨯ Y) ⨯ Z ≅ Z ⨯ (Y ⨯ X) := by
  cat_rw [prod.associator]
  -- Target: X ⨯ (Y ⨯ Z) ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.braiding X (Y ⨯ Z)]
  -- Target: (Y ⨯ Z) ⨯ X ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.associator]
  -- Target: Y ⨯ Z ⨯ X ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.braiding Y (Z ⨯ X)]
  -- Target: (Z ⨯ X) ⨯ Y ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.associator]
  -- Target: Z ⨯ X ⨯ Y ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.braiding X Y]

/-- Testing symmetry flag in rules. -/
example (X Y : C) (h : X ≅ Y) : Y ≅ X := by
  cat_rw [← h]

/-- Mixed products and coproducts with instances. -/
noncomputable
example (X Y Z : C) : (X ⨿ Y) ⨯ Z ≅ (Y ⨿ X) ⨯ Z := by
  cat_rw [coprod.braiding X Y]

/-- Test case from FlashyExample.lean (making it concrete) -/
noncomputable
example (G : C ⥤ D) (X Y : C) [PreservesLimit (pair X Y) G] :
    G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y := by
  let iso := PreservesLimitPair.iso G X Y
  cat_rw [iso]

/-- Double negation (symm of symm). -/
example (X Y : C) (h : X ≅ Y) : X ≅ Y := by
  cat_rw [← (h.symm)]

/-- Identity functor test. -/
example (X : C) : (𝟭 C).obj X ≅ X := by
  apply Iso.refl
