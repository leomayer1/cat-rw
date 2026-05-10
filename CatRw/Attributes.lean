import CatRw.Attr
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Comma.Basic

attribute [cat_rw]
  CategoryTheory.Iso.isZero_iff
  CategoryTheory.Functor.preservesMonomorphisms.iso_iff
  CategoryTheory.Functor.preservesEpimorphisms.iso_iff
  CategoryTheory.Functor.isEquivalence_iff_of_iso
  CategoryTheory.Functor.initial_natIso_iff
  CategoryTheory.Limits.hasLimit_iff_of_iso
  CategoryTheory.Limits.hasColimit_iff_of_iso
  CategoryTheory.Projective.iso_iff
  CategoryTheory.Injective.iso_iff
  CategoryTheory.Simple.iff_of_iso

attribute [cat_rw_iso]
  CategoryTheory.Functor.mapIso
  CategoryTheory.Iso.app
  CategoryTheory.Iso.prod
  CategoryTheory.Comma.leftIso
  CategoryTheory.Comma.rightIso
  CategoryTheory.Limits.prod.mapIso
  CategoryTheory.Limits.coprod.mapIso
  CategoryTheory.MonoidalCategory.whiskerLeftIso
  CategoryTheory.MonoidalCategory.whiskerRightIso
