module

public import Nemonuri.Relations.Heterogeneous.IsBiUnique.SetLike

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} {rel: αl → αr → Prop} {sl: Set αl} {sr: Set αr}


namespace SumUnion

def toSet [IsBiUnique rel] (su: SumUnion (SetHEq rel)) : Set (SumUnion rel) :=
  su.funElim (setOfLeftSet rel) (setOfRightSet rel) (by
    intro l r lm1
    dsimp [setHEq_def] at lm1
    exact lm1 )

theorem toSet_injective [IsBiUnique rel] : Function.Injective (toSet: SumUnion (SetHEq rel) → Set (SumUnion rel)) := by
  intro su1 su2 lm1
  cases su1 using indOfSum
  cases su2 using indOfSum
  rename_i s1 s2
  dsimp [toSet, funElim_eq_ofSum] at lm1
  rcases s1 with ⟨sl1⟩ | ⟨sr1⟩
  <;> rcases s2 with ⟨sl2⟩ | ⟨sr2⟩
  <;> dsimp at lm1
  · rewrite [setOfLeftSet_injective.eq_iff] at lm1
    subst lm1
    rfl
  · simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inl_inr_iff]
    dsimp [setHEq_def]
    exact lm1
  · simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inl_iff]
    dsimp [setHEq_def]
    exact lm1.symm
  · rewrite [setOfRightSet_injective.eq_iff] at lm1
    subst lm1
    rfl

instance [IsBiUnique rel] : SetLike (SumUnion (SetHEq rel)) (SumUnion rel) where
  coe := toSet
  coe_injective := toSet_injective

def iSetElim₂ [IsBiUnique rel] {βl βr: Type*} (rel2: βl → βr → Prop) (isl: αl → Set βl) (isr: αr → Set βr)
              (req: ∀l r, rel l r → SetHEq rel2 (isl l) (isr r))
              (su: SumUnion rel) : SumUnion (SetHEq rel2) :=
    su.funElim (fun l => SumUnion.ofSum (.inl (isl l))) (fun r => SumUnion.ofSum (.inr (isr r))) (by
      intro l r lm1
      simp [ofSum_eq_iff_sumEquivGen]
      refine .rel _ _ ?_
      refine .intro _ _ ?_
      exact req l r lm1 )

/-
instance [IsBiUnique rel] (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : SetLike (SumUnion (SetLikeHEq rel Sαl Sαr)) (SumUnion rel) where
  coe := toSet
-/

/-
theorem rightOfRel?_eq_some_iff_projectLeftSetToRightSet_eq
  {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] [HasPartialCongruence (SetHEq rel)] {sal: Sαl} {sar: Sαr}
  : (HasPartialCongruence.rightOfRel? (SetHEq rel) sal = .some sar) ↔ (projectLeftSetToRightSet rel sal = sar) := by
  simp [HasPartialCongruence.rightOfRel?_eq_some_iff_rel]
-/

end SumUnion

--#check SumUnion.SetLikeHEq

def SetLikeUnion (rel: αl → αr → Prop) (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : Type _ := SumUnion (SumUnion.SetLikeHEq rel Sαl Sαr)

@[defeq]
theorem setLikeUnion_def {rel: αl → αr → Prop} {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] : SetLikeUnion rel Sαl Sαr = SumUnion (SumUnion.SetLikeHEq rel Sαl Sαr) := rfl


namespace SetLikeUnion

open SumUnion

variable {rel: αl → αr → Prop} {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr]

--def toSumUnion (slu: SetLikeUnion rel Sαl Sαr) : SumUnion (SetLikeHEq rel Sαl Sαr) := slu

variable (rel Sαl Sαr) in
def ofSumUnion (su: SumUnion (SetLikeHEq rel Sαl Sαr)) : SetLikeUnion rel Sαl Sαr := su

variable [IsBiUnique rel]

def toSetUnion (slu: SetLikeUnion rel Sαl Sαr) : SumUnion (SetHEq rel) := --slu.toSumUnion.liftOfSum (fun s =>)
  let sumFun : (Sαl ⊕ Sαr) → ((Set αl) ⊕ (Set αr))
    | .inl sal => .inl sal
    | .inr sar => .inr sar
  (slu: SumUnion (SetLikeHEq rel Sαl Sαr)).liftOfSum (.ofSum ∘ sumFun) (by
    intro su1 su2 lm1
    simp [ofSum_eq_iff_sumEquivGen]
    rcases su1 with ⟨sl1⟩ | ⟨sr1⟩
    <;> rcases su2 with ⟨sl2⟩ | ⟨sr2⟩
    <;> (subst sumFun; dsimp)
    · simp [sumEquivGen_inl_inl_iff] at ⊢ lm1
      exact lm1
    · simp [sumEquivGen_inl_inr_iff, setLikeHEq_def] at ⊢ lm1
      exact lm1
    · simp [sumEquivGen_inr_inl_iff, setLikeHEq_def] at ⊢ lm1
      exact lm1
    · simp [sumEquivGen_inr_inr_iff] at ⊢ lm1
      exact lm1 )

theorem toSetUnion_injective : Function.Injective (toSetUnion: SetLikeUnion rel Sαl Sαr → _) := by
  intro slu1 slu2 lm1
  dsimp [setLikeUnion_def] at slu1 slu2
  cases slu1 using indInlInrOfSum
  <;> cases slu2 using indInlInrOfSum
  <;> (dsimp [toSetUnion, liftOfSum_ofSum] at lm1)
  · simp [inl_eq_inl_iff_eq] at lm1
    subst lm1
    rfl
  · simp [inl_eq_inr_iff_rel] at lm1
    refine ofSum_eq_iff_sumEquivGen.mpr ?_
    simp [sumEquivGen_inl_inr_iff]
    exact lm1
  · simp [inr_eq_inl_iff_rel] at lm1
    refine ofSum_eq_iff_sumEquivGen.mpr ?_
    simp [sumEquivGen_inr_inl_iff]
    exact lm1
  · simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inr_iff] at lm1
    subst lm1
    rfl

def toSet (slu: SetLikeUnion rel Sαl Sαr) : Set (SumUnion rel) := slu.toSetUnion.toSet

theorem toSet_injective : Function.Injective (toSet: SetLikeUnion rel Sαl Sαr → _) := SumUnion.toSet_injective.comp toSetUnion_injective


instance : SetLike (SetLikeUnion rel Sαl Sαr) (SumUnion rel) where
  coe := toSet
  coe_injective := toSet_injective


end SetLikeUnion


end Nemonuri.Relations.Heterogeneous

end
