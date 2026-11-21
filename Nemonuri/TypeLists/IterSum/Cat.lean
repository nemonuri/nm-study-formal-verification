module


public import Nemonuri.TypeLists.IterSum.Basic
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists.IterSum

universe u u2


structure OfPi (Pi: (Type u) → List (Type u) → ℕ → ℕ → Sort u2) (Ty: Type u) (tys: List (Type u)) where
  iterSum: IterSum Ty tys


/-
structure CatIdx (Pi: (Type u) → List (Type u) → ℕ → ℕ → Sort u2) (Ty: Type u) (tys: List (Type u)) where
  val: ℕ
  isLt: val < tys.length + 1
-/

namespace CatIdx

instance (Pi: (Type u) → List (Type u) → ℕ → ℕ → Sort u2) (Ty: Type u) (tys: List (Type u)) (i1 i2: ℕ) : FunLike (Pi Ty tys i1 i2) (Indexed Ty tys i1) (Indexed Ty tys i2) where


end CatIdx


structure CatStruct (Pi: (Type u) → List (Type u) → ℕ → ℕ → Sort u2) (Ty: Type u) (tys: List (Type u)) where
  hom (i1 i2: ℕ) : Pi Ty tys i1 i2
  id (i: ℕ) : Pi Ty tys i i
  comp (i1 i2 i3: ℕ) : Pi Ty tys i1 i2 → Pi Ty tys i2 i3 → Pi Ty tys i1 i3
/-
  hom (isum1 isum2: IterSum Ty tys): Pi Ty tys isum1.valIndex isum2.valIndex
  id (idx: ℕ) : Pi Ty tys idx idx
  comp (isum1 isum2 isum3: IterSum Ty tys) :
      (Pi Ty tys isum1.valIndex isum2.valIndex) →
      (Pi Ty tys isum2.valIndex isum3.valIndex) →
      (Pi Ty tys isum1.valIndex isum3.valIndex)
-/

structure IsCat (Pi: (Type u) → List (Type u) → ℕ → ℕ → Sort u2) (Ty: Type u) (tys: List (Type u)) (s: CatStruct Pi Ty tys) : Prop where
  id_comp (i1 i2: ℕ) :


/-

  mod_eq (idx: ℕ) : Pi Ty tys idx idx = Pi Ty tys (idx % (tys.length + 1)) (idx % (tys.length + 1))
  id_comp (idx1 idx2: ℕ) (f: Pi Ty tys idx1 idx2) : s.comp (s.id idx1)
-/



end Nemonuri.TypeLists.IterSum


end
