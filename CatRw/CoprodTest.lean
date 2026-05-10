import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasBinaryProducts C] [HasBinaryCoproducts C]
variable {D : Type*} [Category* D]
variable {F G : C ⥤ D}
variable (a a' b c b' : C)

set_option linter.style.setOption false
set_option trace.CatRw true

set_option warn.sorry false

example (ha : a ≅ a') : IsZero (a ⨿ b) := by
  cat_rw [ha]
  admit

example (ha : a ≅ a') : IsZero (a ⨯ b) := by
  cat_rw [ha]
  -- cat_rw [ha] should make the goal ⊢ IsZero (a' ⨯ b)
  sorry

noncomputable example (ha : a ≅ a') (hb : b ≅ b') : a ⨯ b ⨯ c ≅ a' ⨯ b' ⨯ c := by
  cat_rw [ha, hb]

example (ha : a ≅ a') : IsZero (a ⨿ b) := by
  -- cat_rw [ha] should make the goal ⊢ IsZero (a' ⨿ b)
  sorry

example (φ : F ≅ G) (ha : a ≅ a') :
    IsZero (F.obj (a ⨯ b ⨯ a)) := by
  cat_rw [ha, ha]
  sorry
