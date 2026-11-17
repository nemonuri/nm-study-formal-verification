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


inductive ReflSymmOfFin {tys: List (Type u)} (iter: IterHRel tys) : (i1: Fin tys.length) → iter.types[i1] → (i2: Fin tys.length) → iter.types[i2] → Prop where
  | rel (i1 i2: Fin tys.length) (req: i1 < i2) (v1: iter.types[i1]) (v2: iter.types[i2]) : ReflSymmOfFin iter i1 v1 i2 v2
  | refl (i: Fin tys.length) (v: iter.types[i]) : ReflSymmOfFin iter i v i v
  | rel_symm (i1 i2: Fin tys.length) (req: i1 < i2) (v1: iter.types[i1]) (v2: iter.types[i2]) : ReflSymmOfFin iter i2 v2 i1 v1

/-
  symm (i1: Fin tys.length) (v1: iter.types[i1]) (i2: Fin tys.length) (v2: iter.types[i2]) (req: i2 < i1)
        : ReflSymmOfFin iter i1 v1 i2 v2 → ReflSymmOfFin iter i2 v2 i1 v1
-/

def IterSumRel {tys: List (Type u)} (iter: IterHRel tys) (isum1 isum2: IterSum tys) : Prop :=
  iter.ReflSymmOfFin isum1.valIndexFin isum1.valAsGetElem isum2.valIndexFin isum2.valAsGetElem

@[defeq]
theorem iterSumRel_def {tys: List (Type u)} {iter: IterHRel tys} {isum1 isum2: IterSum tys}
  : IterSumRel iter isum1 isum2 = iter.ReflSymmOfFin isum1.valIndexFin isum1.valAsGetElem isum2.valIndexFin isum2.valAsGetElem :=
  rfl


namespace IterSumRel

variable {tys: List (Type u)} {irel: IterHRel tys}

@[refl]
protected theorem refl (isum: IterSum tys) : irel.IterSumRel isum isum := by
  dsimp [iterSumRel_def]
  exact .refl isum.valIndexFin isum.valAsGetElem

open IterSum in
@[symm]
protected theorem symm {isum1 isum2: IterSum tys} (h: irel.IterSumRel isum1 isum2) : irel.IterSumRel isum2 isum1 := by
  dsimp [iterSumRel_def] at ⊢ h
  cases isum1 with
  | ofVal Ty tys v1 =>
    cases isum2 with
    | ofVal _ _ v2 =>
      cases h with
      | rel _ _ lm1 => simp [ofVal_valIndexFin_eq_zero] at lm1
      | refl => exact .refl _ _
      | rel_symm _ _ lm1 => simp [ofVal_valIndexFin_eq_zero] at lm1
    | cons _ _ isum =>


  --exact .symm _ _ _ _ h

instance : Std.Refl irel.IterSumRel := ⟨IterSumRel.refl⟩

instance : Std.Symm irel.IterSumRel := ⟨fun _ _ => IterSumRel.symm⟩

/-
open IterSum in
theorem ofVal_ofVal_to_val_eq {Ty: Type u} {v1 v2: Ty} {irel: IterHRel (Ty::tys)} (h: IterSumRel irel (ofVal Ty tys v1) (ofVal Ty tys v2)) : v1 = v2 := by
  cases h with
  | rel _ _ lm1 => simp [ofVal_valIndexFin_eq_zero] at lm1
  | refl => rfl
  | symm _ _ _ _ lm1 =>
-/



/-
open IterSum in
theorem ofVal_iff {Ty: Type u} (v1 v2: Ty) (irel: IterHRel (Ty::tys)) : (IterSumRel irel (ofVal Ty tys v1) (ofVal Ty tys v2)) ↔ (v1 = v2) := by
  --dsimp [iterSumRel_def]
-/

end IterSumRel


inductive IterRelDep.{u2} (D: (Ty1 Ty2: Type u) → (rel: Ty1 → Ty2 → Prop) → Sort u2) : (tys: List (Type u)) → (IterHRel tys) → Sort _ where
  | single (Head: Type u) : IterRelDep D [Head] (.single Head)
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (rel: Head1 → Head2 → Prop) (dep: D _ _ rel)
         (iter1: IterHRel (Head1 :: tail)) (iterD1: IterRelDep D (Head1 :: tail) iter1)
         (iter2: IterHRel (Head2 :: tail)) (iterD2: IterRelDep D (Head2 :: tail) iter2)
         : IterRelDep D (Head1 :: Head2 :: tail) (.cons Head1 Head2 tail rel iter1 iter2)

abbrev IterBiUnique {tys: List (Type u)} (irel: (IterHRel tys)) : Type _ := IterRelDep (fun _ _ rel => Relator.BiUnique rel) tys irel

@[defeq]
theorem iterBiUnique_def {tys: List (Type u)} {irel: (IterHRel tys)} : IterBiUnique irel = IterRelDep (fun _ _ rel => Relator.BiUnique rel) tys irel :=
  rfl

abbrev IterDecidableRel {tys: List (Type u)} (irel: (IterHRel tys)) : Type _ := IterRelDep (fun _ _ rel => DecidableRel rel) tys irel

@[defeq]
theorem iterDecidableRel_def {tys: List (Type u)} {irel: (IterHRel tys)} : IterDecidableRel irel = IterRelDep (fun _ _ rel => DecidableRel rel) tys irel :=
  rfl


namespace IterSumRel

variable {tys: List (Type u)} {irel: IterHRel tys}

open IterSum in
protected theorem trans (ibu: irel.IterBiUnique) (isum1 isum2 isum3: IterSum tys)
  (h1: irel.IterSumRel isum1 isum2) (h2: irel.IterSumRel isum2 isum3) : irel.IterSumRel isum1 isum3 := by
  --dsimp [iterSumRel_def] at h1 h2 ⊢
  induction isum1 with
  | ofVal Ty1 tys v1 =>
    cases isum2 with
    | ofVal _ _ v2 =>
      cases isum3 with
      | ofVal _ _ v3 =>


/-
  dsimp [iterBiUnique_def] at ibu
  cases ibu with
  | single Ty =>
    dsimp [iterSumRel_def] at h1 h2 ⊢
    rcases isum1 --(try (refine IterSum.elimNil ?_; assumption))
    <;> rcases isum2
    <;> rcases isum3
    <;> try (refine IterSum.elimNil ?_; assumption)
    rename_i v1 v2 v3
    dsimp [IterSum.types] at h1 h2
-/
    --dsimp only [valAsGetElem] at h1 h2
    --rw [ofVal_valIndexFin_eq_zero] at h1 h2
    --rewrite [ofVal_valIndex_eq_zero] at h1 h2
    --generalize lm1: (ofVal Ty [] v1) = isum1 at h1 h2
    --generalize lm2: (ofVal Ty [] v2) = isum2 at h1 h2
    --have lm3 :=
/-
    cases h1 with
    | rel _ _ lm1 =>
      dsimp [valIndexFin] at lm1
      rw [Fin.mk_lt_mk] at lm1
      dsimp [valIndex] at lm1
      unfold valIndexAt at lm1
      simp only at lm1
      exact Nat.not_lt_zero _ lm1 |>.elim
    | refl => exact h2
    | symm _ _ _ _ lm1 =>
-/




end IterSumRel




end IterHRel

end Nemonuri.TypeLists

end
