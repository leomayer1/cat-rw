import Mathlib
import CatRw.Tactic

open CategoryTheory Limits AlgebraicGeometry

variable {C : Type*} [Category* C] (X Y : C) (φ : X ≅ Y) {D : Type*} [Category* D] (F : C ⥤ D)

example (h : IsZero Y) : IsZero X := by
    cat_rw [φ]
    exact h

example (h : IsZero Y) : IsZero X := by
    rw [Iso.isZero_iff φ]
    exact h

example (F G : C ⥤ D) (φ : F ≅ G) [G.PreservesMonomorphisms] :
        F.PreservesMonomorphisms := by
    cat_rw [φ]
    infer_instance

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
