import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasProducts C] [HasBinaryCoproducts C]
variable {D : Type*} [Category* D]
variable {F G : C ⥤ D}
variable (a a' b : C)

example (ha : a ≅ a') : IsZero (a ⨿ b) := by
  -- cat_rw [ha] should make the goal ⊢ IsZero (a' ⨿ b)
  sorry
