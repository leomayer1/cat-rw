import CatRw.BasicV2
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory Limits

set_option linter.style.setOption false
set_option trace.CatRw false

set_option warn.sorry false

variable {C : Type*} [Category C] [HasBinaryProducts C] [HasZeroObject C]

/-- Test `at` location. -/
noncomputable
example (X Y Z : C) (h : X ≅ Y) (hl : X ⨯ Z ≅ Z) : Y ⨯ Z ≅ Z := by
  cat_rw [h] at hl
  exact hl

/-- Test `occs`. -/
noncomputable
example (X Y : C) (h : X ≅ Y) : (X ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X := by
  -- Should rewrite only the first X on the LHS
  cat_rw (config := { occs := .pos [1] }) [h]
  guard_target = (Y ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X
  admit

noncomputable
example (X Y : C) (h : X ≅ Y) : (X ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X := by
  -- Should rewrite only the second X on the LHS
  cat_rw (config := { occs := .pos [2] }) [h]
  guard_target = (X ⨯ Y) ⨯ X ≅ (X ⨯ X) ⨯ X
  admit

noncomputable
example (X Y : C) (h : X ≅ Y) : (X ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X := by
  -- Should rewrite only the third X on the LHS
  cat_rw (config := { occs := .pos [3] }) [h]
  guard_target = (X ⨯ X) ⨯ Y ≅ (X ⨯ X) ⨯ X
  admit
