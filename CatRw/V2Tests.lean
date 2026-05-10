import CatRw.BasicV2
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso

open CategoryTheory Limits

set_option linter.style.setOption false
set_option trace.CatRw false
set_option CatRw.trace_iso_expr true
set_option warn.sorry false

variable {C : Type*} [Category C] [HasBinaryProducts C] [HasBinaryCoproducts C] [HasZeroObject C]

/-- Basic isomorphism rewrite. -/
noncomputable
example (X Y Z : C) (h : X ≅ Y) : X ⨯ Z ≅ Y ⨯ Z := by
  cat_rwv2 [h]

/-- Goal rewrite. -/
example (X Y : C) (h : X ≅ Y) (hz : IsZero X) : IsZero Y := by
  cat_rwv2 [← h]
  exact hz

/-- Equality rewrite (generalized). -/
example (n m : Nat) (h : n = m) : 0 + n = m := by
  cat_rwv2 [h]
  rw [Nat.zero_add]
