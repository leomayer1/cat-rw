import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasBinaryCoproducts C]
variable (a a' b : C)

set_option trace.CatRw true in
example (ha : a ≅ a') : IsZero (a ⨿ b) := by
  cat_rw [ha]
  sorry
