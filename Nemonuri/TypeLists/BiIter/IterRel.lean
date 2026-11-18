module


public import Nemonuri.TypeLists.BiIter.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists.BiIter


universe u


def IterRel₂ (tys: List (Type u)) : Type _ := BiIter₂ (fun Ty1 Ty2 => Ty1 → Ty2 → Prop) tys

@[defeq]
theorem iterRel₂_def {tys: List (Type u)} : IterRel₂ tys = BiIter₂ (fun Ty1 Ty2 => Ty1 → Ty2 → Prop) tys := rfl


namespace IterRel₂

def SumRel {tys: List (Type u)} (irel: IterRel₂ tys) (isum1 isum2: IterSum tys) : Prop :=
  BiIter₂.getOfIterSum irel isum1 isum2 (fun _ => Eq) (fun _ _ rel => flip rel) isum1.val isum2.val

@[defeq]
theorem sumRel_def {tys: List (Type u)} {irel: IterRel₂ tys} {isum1 isum2: IterSum tys}
  : SumRel irel isum1 isum2 = BiIter₂.getOfIterSum irel isum1 isum2 (fun _ => Eq) (fun _ _ rel => flip rel) isum1.val isum2.val :=
  rfl

namespace SumRel

--variable {tys: List (Type u)}

@[refl]
protected theorem refl {tys: List (Type u)} (irel: IterRel₂ tys) (isum: IterSum tys) : irel.SumRel isum isum := by
  dsimp [SumRel]
  cases irel with
  | single _ =>
    cases isum using IterSum.recSingleOn
    dsimp
  | cons _ Ty2 tys bi1 bi2 =>
    cases isum with
    | ofVal _ => dsimp
    | cons _ _ isum =>
      dsimp
      exact SumRel.refl bi2 isum


@[symm]
protected theorem symm {tys: List (Type u)} (irel: IterRel₂ tys) (isum1 isum2: IterSum tys) (req: irel.SumRel isum1 isum2) : irel.SumRel isum2 isum1 := by
  dsimp [SumRel] at ⊢ req
  cases irel with
  | single _ =>
    cases isum1 using IterSum.recSingleOn
    cases isum2 using IterSum.recSingleOn
    dsimp at ⊢ req
    exact req.symm
  | cons _ _ _ bi1 bi2 =>
    rcases bi1
    rcases isum1
    <;> rcases isum2
    <;> (dsimp [flip] at ⊢ req)
    <;> (try exact req)
    · exact req.symm
    · exact SumRel.symm bi2 _ _ req


instance {tys: List (Type u)} (irel: IterRel₂ tys) : Std.Refl irel.SumRel where
  refl := SumRel.refl irel

instance {tys: List (Type u)} (irel: IterRel₂ tys) : Std.Symm irel.SumRel where
  symm := SumRel.symm irel

open IterSum

theorem single_iff_val_heq (Ty: Type u) (irel: IterRel₂ [Ty]) (isum1 isum2: IterSum [Ty]) : irel.SumRel isum1 isum2 ↔ (isum1.val ≍ isum2.val) := by
  rcases irel
  cases isum1 using recSingleOn
  cases isum2 using recSingleOn
  dsimp [sumRel_def]
  exact heq_iff_eq.symm

theorem single_iff_eq (Ty: Type u) (irel: IterRel₂ [Ty]) (isum1 isum2: IterSum [Ty]) : irel.SumRel isum1 isum2 ↔ (isum1 = isum2) := by
  constructor
  · intro lm1
    have lm2 := single_iff_val_heq _ _ _ _ |>.mp lm1
    refine IterSum.ext _ _ _ ?_ lm2
    simp only [single_valIndex]
  · intro lm1
    subst lm1
    rfl


theorem ofVal_ofVal_iff_eq (Ty: Type u) (tys: List (Type u)) (irel: IterRel₂ (Ty::tys)) (v1 v2: Ty)
  : irel.SumRel (.ofVal _ _ v1) (.ofVal _ _ v2) ↔ v1 = v2 := by
  rcases irel
  · simp [single_iff_val_heq]
  · dsimp [sumRel_def]
    rfl


theorem ofVal_ofVal_refl (Ty: Type u) (tys: List (Type u)) (irel: IterRel₂ (Ty::tys)) (v: Ty) : irel.SumRel (.ofVal _ _ v) (.ofVal _ _ v) :=
  (ofVal_ofVal_iff_eq _ _ irel v v).mpr (Eq.refl v)


theorem cons_cons_iff_tail (Ty1 Ty2: Type u) (tys: List (Type u)) (irel: IterRel₂ (Ty1::Ty2::tys)) (isum1 isum2: IterSum (Ty2::tys))
  : irel.SumRel (.cons _ _ isum1) (.cons _ _ isum2) ↔ SumRel (irel.tail) isum1 isum2 := by
  rcases irel
  dsimp [sumRel_def]
  rfl


theorem eq_of_valIndex_eq {tys: List (Type u)} {irel: IterRel₂ tys} {isum1 isum2: IterSum tys} (h: irel.SumRel isum1 isum2) (req: isum1.valIndex = isum2.valIndex)
  : isum1 = isum2 := by
  cases irel with
  | single Ty => exact single_iff_eq _ _ _ _ |>.mp h
  | cons _ _ _ bi1 bi2 =>
    rcases isum1 <;> rcases isum2
    <;> simp at req
    · simp only [ofVal_ofVal_iff_eq] at h
      simp
      exact h
    · simp [cons_cons_iff_tail] at h
      simp
      exact eq_of_valIndex_eq h req






/-
theorem sumRel_iff_of_valIndex_eq (tys: List (Type u)) (irel: IterRel₂ tys) (isum1 isum2: IterSum tys) (req: isum1.valIndex = isum2.valIndex)
  : irel.SumRel isum1 isum2 ↔ (isum1 = isum2) := by
-/



end SumRel

/-
open IterSum in
theorem sumRel_iff {tys: List (Type u)} {irel: IterRel₂ tys} {isum1 isum2: IterSum tys} : irel.SumRel isum1 isum2 := by
  cases irel with
  | single Ty =>
    cases isum1 using recSingleOn
    cases isum2 using recSingleOn
    dsimp [sumRel_def]
-/



end IterRel₂

end Nemonuri.TypeLists.BiIter

end
