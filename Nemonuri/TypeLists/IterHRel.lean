module


public import Nemonuri.TypeLists.IterSum

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists


inductive IterHRel.{u} : List (Type u) → Type _ where
  | single (Head: Type u) : IterHRel [Head]
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (rel: Head1 → Head2 → Prop) : IterHRel (Head1 :: tail) → IterHRel (Head2 :: tail) → IterHRel (Head1 :: Head2 :: tail)


namespace IterHRel

universe u

abbrev types {tys: List (Type u)} (_: IterHRel tys) : List (Type u) := tys



def OfFinLt {tys: List (Type u)} (iter: IterHRel tys) (i1 i2: Fin tys.length) (req: i1 < i2) : iter.types[i1] → iter.types[i2] → Prop :=
  match tys, iter with
  | [Ty], .single _ => False.elim (by rcases i1 with ⟨i1, lm1⟩; rcases i2 with ⟨i2, lm2⟩; simp at lm1 lm2 req; simp [lm1, lm2] at req)
  | Ty1::Ty2::tys, .cons _ _ _ rel iter1 iter2 =>
  let ⟨i1, lm1⟩ := i1
  let ⟨i2, lm2⟩ := i2
  match i1 with
  | 0 =>
    match i2 with
    | 0 => False.elim (by simp at req)
    | 1 => rel
    | i2 + 2 =>
      OfFinLt iter1 ⟨0, (by simp)⟩ ⟨(i2 + 1), (by simp at lm2 ⊢; exact lm2)⟩ (by rw [Fin.mk_lt_mk]; simp) --|> cast (by dsimp)
  | i1 + 1 =>
    match i2 with
    | 0 | 1 => False.elim (by rw [Fin.mk_lt_mk] at req; simp at req)
    | i2 + 2 =>
      OfFinLt iter2 ⟨i1, (by simp at lm1 ⊢; exact lm1)⟩ ⟨(i2 + 1), (by simp at ⊢ lm2; exact lm2)⟩ (by rw [Fin.mk_lt_mk] at ⊢ req; simpa using req)


inductive ReflSymmOfFin {tys: List (Type u)} (iter: IterHRel tys) : (i1: Fin tys.length) → (i2: Fin tys.length) → iter.types[i1] → iter.types[i2] → Prop where
  | ofEq (i: Fin tys.length) (v: iter.types[i]) : ReflSymmOfFin iter i i v v
  | ofLt (i1 i2: Fin tys.length) (req: i1 < i2) (v1: iter.types[i1]) (v2: iter.types[i2]) : ReflSymmOfFin iter i1 i2 v1 v2
  | ofGt (i1 i2: Fin tys.length) (req: i1 < i2) (v1: iter.types[i1]) (v2: iter.types[i2]) : ReflSymmOfFin iter i2 i1 v2 v1

def OfIterSum {tys: List (Type u)} (iter: IterHRel tys) (isum1 isum2: IterSum tys) : Prop :=
  iter.ReflSymmOfFin isum1.valIndexFin isum2.valIndexFin isum1.valAsGetElem isum2.valAsGetElem

--inductive IterSumRelGen {tys: List (Type u)} (iter: IterHRel tys) : (IterSum tys) → (IterSum tys) → Prop where


/-
  | 1 =>
    match i2 with
    | 0 | 1 => False.elim (by simp at req)
    | i2 + 2 =>
      HRelOfFinLt iter2 ⟨0, (by simp)⟩ ⟨(i2 + 1), (by simp at ⊢ lm2; exact lm2)⟩ (by rw [Fin.mk_lt_mk]; simp)
  | i1 + 2 =>
    HRelOfFinLt iter2 ⟨()
-/

/-
def HRel {Ty1 Ty2: Type u} {tys: List (Type u)} : IterHRel (Ty1 :: Ty2 :: tys) → Ty1 → Ty2 → Prop
  | .cons _ _ rel _ _ => rel
-/

/-
def HRelOfFinLt {tys: List (Type u)} (iter: IterHRel tys) (i1 i2: Fin tys.length) (req: i1 < i2) : iter.types[i1] → iter.types[i2] → Prop :=
  match tys with
  | [] => i1.elim0
  | Ty1::tys =>
  match tys with
  | [] =>
    match iter with
    | .single _ => False.elim (by rcases i1 with ⟨i1, lm1⟩; rcases i2 with ⟨i2, lm2⟩; simp at lm1 lm2 req; simp [lm1, lm2] at req)
  | Ty2::tys =>
  match iter with
  | .cons _ _ rel _ iter =>
  let ⟨i1, lm1⟩ := i1
  let ⟨i2, lm2⟩ := i2
  match i1 with
  | 0 =>
    match i2 with
    | 0 => False.elim (by simp at req)
    | 1 => rel
    | i2 + 1 + 1 =>
      HRelOfFinLt iter ⟨0, (by simp)⟩ ⟨(i2 + 1), (by simp at lm2 ⊢; exact lm2)⟩ (by rw [Fin.mk_lt_mk]; simp) |> cast (by dsimp)
  | i1 + 1 =>
-/
/-
  match i1 with
  | 0 =>
    match i2 with
    | 0 => False.elim (by simp)
-/
/-
inductive IterSumRelGen : {tys: List (Type u)} → (IterHRel tys) → (IterSum tys) → (IterSum tys) → Prop where
  | rel (Head1 Head2: Type u) (rel: Head1 → Head2 → Prop) (tail: List (Type u)) (iter: IterHRel (Head1 :: tail))
-/


/-
inductive Perm : {tys1: List (Type u)} → (IterHRel tys1) → {tys2: List (Type u)} → (IterHRel tys2) → Prop where
  | single (Ty: Type u) : Perm (.single Ty) (.single Ty)
  | cons (Ty1 Ty2: Type u) (rel: Ty1 → Ty2 → Prop)
         (tys1: List (Type u)) (iter1: IterHRel (Ty1 :: tys1))
         (tys2: List (Type u)) (iter2: IterHRel (Ty1 :: tys2))
         : Perm iter1 iter2 → Perm (.cons Ty1 Ty2 rel tys1 iter1) (.cons Ty1 Ty2 rel tys2 iter2)
  | swap (Ty1 Ty2: Type u) (rel: Ty1 → Ty2 → Prop) --(rel2: Ty2 → Ty3 → Prop)
         (tys: List (Type u)) (iter1: IterHRel (Ty1 :: tys)) (iter2: IterHRel (Ty2 :: tys))
         : Perm (.cons Ty1 Ty2 rel tys iter1) (.cons Ty2 Ty1 (flip rel) tys iter2)
  | trans (tys1 tys2 tys3: List (Type u)) (iter1: IterHRel tys1) (iter2: IterHRel tys2) (iter3: IterHRel tys3)
         : Perm iter1 iter2 → Perm iter2 iter3


inductive ReflSymmRel : {tys: List (Type u)} → (iter: IterHRel tys) → (Ty1: Type u) → (Ty2: Type u) → Ty1 → Ty2 → Prop where
  | refl (Ty: Type u) (v: Ty) : ReflSymmRel (.single Ty) Ty Ty v v
  | rel (Ty1 Ty2: Type u) (v1: Ty1) (v2: Ty2) (tys: List (Type u)) (iter: IterHRel [Ty1, Ty2]) (req: iter.HRel v1 v2) : ReflSymmRel iter Ty1 Ty2 v1 v2
  | perm (Ty1 Ty2: Type u) (v1: Ty1) (v2: Ty2) (tys1: List (Type u)) (iter1: IterHRel tys1) (tys2: List (Type u)) (iter2: IterHRel tys2)
         : Perm iter1 iter2 → ReflSymmRel iter1 Ty1 Ty2 v1 v2 → ReflSymmRel iter2 Ty1 Ty2 v1 v2
  | cons (Ty1 Ty2: Type u) (v1: Ty1) (v2: Ty2) (tys: List (Type u)) (iter1: IterHRel tys) (Ty3: Type u) (iter2: IterHRel (Ty3::tys))
         : ReflSymmRel iter1 Ty1 Ty2 v1 v2 → ReflSymmRel iter2 Ty1 Ty2 v1 v2
-/




/-
inductive ReflSymm : {tys: List (Type u)} → (iter: IterHRel tys) → (Ty1: Type u) → (Ty2: Type u) → Ty1 → Ty2 → Prop where
  | single (Ty: Type u) (v: Ty) : ReflSymm (.single Ty) Ty Ty v v
  | cons (Ty1 Ty2: Type u) (rel: Ty1 → Ty2 → Prop) (v1: Ty1) (v2: Ty2) (req: rel v1 v2) (tys: List (Type u)) (iter: IterHRel (Ty1 :: tys))
    : ReflSymm (.cons Ty1 Ty2 rel tys iter) Ty1 Ty2 v1 v2
-/

end IterHRel

end Nemonuri.TypeLists

end
