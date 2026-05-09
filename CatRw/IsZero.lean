import Mathlib

open CategoryTheory Limits

variable {C : Type*} [Category* C] (X Y : C) (φ : X ≅ Y) {D : Type*} [Category* D] (F : C ⥤ D)

example (h : IsZero Y) : IsZero X := by
    rw [Iso.isZero_iff φ] -- cat_rw [φ]
    exact h

example (h : IsZero (F.obj Y)) : IsZero (F.obj X) := by
    let φ : F.obj X ≅ F.obj Y := F.mapIso φ
    rw [Iso.isZero_iff φ]
    exact h

example {E : Type*} [Category* E] (G : D ⥤ E) (h : IsZero (G.obj (F.obj Y))) :
        IsZero (G.obj (F.obj X)) := by
    let φ : G.obj (F.obj X) ≅ G.obj (F.obj Y) := G.mapIso (F.mapIso φ)
    rw [Iso.isZero_iff φ]
    exact h

example (G : C ⥤ D) (h : IsZero (G.obj X)) (ψ : F ≅ G) : IsZero (F.obj X) := by
    let φ : F.obj X ≅ G.obj X := ψ.app X
    rw [Iso.isZero_iff φ]
    exact h
