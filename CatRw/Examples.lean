import CatRw.Basic
import Mathlib

open CategoryTheory Limits
open scoped MonoidalCategory

section GoalRewrites

variable {J : Type*} [Category J]
variable {C : Type*} [Category C]
variable {F G : J ⥤ C} (η : F ≅ G)

example [HasLimit G] : HasLimit F := by
  cat_rw [η]
  infer_instance

example [HasColimit G] : HasColimit F := by
  cat_rw [η]
  infer_instance

variable {X Y : C} (e : X ≅ Y)

example [Projective Y] : Projective X := by
  cat_rw [e]
  infer_instance

example [Injective Y] : Injective X := by
  cat_rw [e]
  infer_instance

example [HasZeroMorphisms C] (h : Simple Y) : Simple X := by
  cat_rw [e]
  exact h

end GoalRewrites

section Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C]
variable (A : C) {X Y : C} (e : X ≅ Y)

example : A ⊗ X ≅ A ⊗ Y := by
  cat_rw [e]

example : X ⊗ A ≅ Y ⊗ A := by
  cat_rw [e]

end Monoidal

section ModuleCat

variable {R : Type} [CommRing R] (M N P : ModuleCat R)

open BraidedCategory

end ModuleCat

section ProductCategory

variable {C D : Type*} [Category C] [Category D]
variable {X Y : C} {S T : D} (e : X ≅ Y) (f : S ≅ T)

example : (X, S) ≅ (Y, T) := by
  cat_rw [e, f]

end ProductCategory

section Comma

variable {A B T : Type*} [Category A] [Category B] [Category T]
variable {L : A ⥤ T} {R : B ⥤ T}
variable {X Y : Comma L R} (e : X ≅ Y)

example : X.left ≅ Y.left := by
  cat_rw [e]

example : X.right ≅ Y.right := by
  cat_rw [e]

end Comma
