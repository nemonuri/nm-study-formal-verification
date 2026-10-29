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



@[defeq, sum_simp]
theorem toSet_mem_inl_eq [IsBiUnique rel] {su: SumUnion rel} : (su ∈ toSet (.ofSum (.inl sl))) = (su ∈ setOfLeftSet rel sl) := by
  dsimp [toSet, funElim_eq_ofSum]

@[defeq, sum_simp]
theorem toSet_mem_inr_eq [IsBiUnique rel] {su: SumUnion rel} : (su ∈ toSet (.ofSum (.inr sr))) = (su ∈ setOfRightSet rel sr) := by
  dsimp [toSet, funElim_eq_ofSum]



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


theorem indOfSumUnion
  {motive: SetLikeUnion rel Sαl Sαr → Prop}
  (inl: (l: Sαl) → motive (.ofSumUnion rel Sαl Sαr (.ofSum (.inl l))))
  (inr: (r: Sαr) → motive (.ofSumUnion rel Sαl Sαr (.ofSum (.inr r))))
  (t: SetLikeUnion rel Sαl Sαr)
  : motive t :=
  SumUnion.indInlInrOfSum inl inr t


def toSumUnion (slu: SetLikeUnion rel Sαl Sαr) : SumUnion (SumUnion.SetLikeHEq rel Sαl Sαr) := slu

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

@[defeq]
theorem mem_def {slu: SetLikeUnion rel Sαl Sαr} {su: SumUnion rel} : (su ∈ slu) = (su ∈ slu.toSet) := rfl

@[defeq, sum_simp]
theorem mem_inl_eq {su: SumUnion rel} {sal: Sαl} : (su ∈ (ofSumUnion rel Sαl Sαr (.ofSum (.inl sal)))) = (su ∈ setOfLeftSet rel sal) := by
  dsimp [ofSumUnion, mem_def, toSet, toSetUnion, liftOfSum_ofSum, sum_simp]

@[defeq, sum_simp]
theorem mem_inr_eq {su: SumUnion rel} {sar: Sαr} : (su ∈ (ofSumUnion rel Sαl Sαr (.ofSum (.inr sar)))) = (su ∈ setOfRightSet rel sar) := by
  dsimp [ofSumUnion, mem_def, toSet, toSetUnion, liftOfSum_ofSum, sum_simp]


def isMem [HasPartialCongruence rel] [∀(sal: Sαl), DecidablePred (· ∈ sal)] [∀(sar: Sαr), DecidablePred (· ∈ sar)]
  (su: SumUnion rel) (slu: SetLikeUnion rel Sαl Sαr) : Bool :=
  let sumFun (su: SumUnion rel) : (Sαl ⊕ Sαr) → Bool
    | .inl sal => match su.left? with | .some l => decide (l ∈ sal) | .none => .false
    | .inr sar => match su.right? with | .some r => decide (r ∈ sar) | .none => .false
  slu.toSumUnion.liftOfSum (fun x => sumFun su x) (by
    simp [sum_simp]
    refine ⟨?_, ?_⟩
    · intro sal sar lm1
      cases su using indInlInrOfSum with
      | inl l =>
        subst sumFun
        simp [sum_simp]
        split
        · rename_i r lm2
          simp [right?_eq_some_iff_eq, sum_simp] at lm2
          have lm3 := lm1.mem_iff_mem_of_rel l r lm2
          simpa only [decide_eq_decide, SetLike.mem_coe] using lm3
        · rename_i lm2
          simp [sum_simp] at lm2
          dsimp [setLikeHEq_def] at lm1
          rewrite [setHEq_iff_forall_iff_and_forall_iff] at lm1
          rcases lm1 with ⟨lm1_1, lm1_2⟩
          specialize lm1_1 l
          simp [lm2] at lm1_1
          simpa only [decide_eq_false_iff_not] using lm1_1
      | inr r =>
        subst sumFun
        simp [sum_simp]
        split
        · rename_i l lm2
          simp [left?_eq_some_iff_eq, sum_simp] at lm2
          have lm3 := lm1.mem_iff_mem_of_rel l r lm2
          simpa only [decide_eq_decide, SetLike.mem_coe] using lm3
        · rename_i lm2
          simp [sum_simp] at lm2
          dsimp [setLikeHEq_def] at lm1
          rewrite [setHEq_iff_forall_iff_and_forall_iff] at lm1
          rcases lm1 with ⟨lm1_1, lm1_2⟩
          specialize lm1_2 r
          simp [lm2] at lm1_2
          simpa only [false_eq_decide_iff] using lm1_2
    · intro sar sal lm1
      symm
      cases su using indInlInrOfSum with
      | inl l =>
        subst sumFun
        simp [sum_simp]
        split
        · rename_i r lm2
          simp [right?_eq_some_iff_eq, sum_simp] at lm2
          have lm3 := lm1.mem_iff_mem_of_rel l r lm2
          simpa only [decide_eq_decide, SetLike.mem_coe] using lm3
        · rename_i lm2
          simp [sum_simp] at lm2
          dsimp [setLikeHEq_def] at lm1
          rewrite [setHEq_iff_forall_iff_and_forall_iff] at lm1
          rcases lm1 with ⟨lm1_1, lm1_2⟩
          specialize lm1_1 l
          simp [lm2] at lm1_1
          simpa only [decide_eq_false_iff_not] using lm1_1
      | inr r =>
        subst sumFun
        simp [sum_simp]
        split
        · rename_i l lm2
          simp [left?_eq_some_iff_eq, sum_simp] at lm2
          have lm3 := lm1.mem_iff_mem_of_rel l r lm2
          simpa only [decide_eq_decide, SetLike.mem_coe] using lm3
        · rename_i lm2
          simp [sum_simp] at lm2
          dsimp [setLikeHEq_def] at lm1
          rewrite [setHEq_iff_forall_iff_and_forall_iff] at lm1
          rcases lm1 with ⟨lm1_1, lm1_2⟩
          specialize lm1_2 r
          simp [lm2] at lm1_2
          simpa only [false_eq_decide_iff] using lm1_2 )


theorem isMem_eq_true_iff [HasPartialCongruence rel] [∀(sal: Sαl), DecidablePred (· ∈ sal)] [∀(sar: Sαr), DecidablePred (· ∈ sar)]
  {su: SumUnion rel} {slu: SetLikeUnion rel Sαl Sαr} : (slu.isMem su = .true) ↔ (su ∈ slu) := by
  cases slu using indOfSumUnion with
  | inl sal =>
    simp [sum_simp]
    dsimp [isMem, toSumUnion, ofSumUnion, liftOfSum_ofSum]
    generalize lm1: su.left? = l?
    rcases l? with _ | ⟨l⟩
    · cases su using indInlInrOfSum
      <;> simp [sum_simp] at ⊢ lm1
      · simp [lm1]
    · cases su using indInlInrOfSum
      <;> simp [sum_simp] at ⊢ lm1
      · subst lm1; rfl
      · symm
        exact IsBiUnique.left_pred_iff_exists_left_pred_and_rel_of_rel (· ∈ sal) lm1
  | inr sar =>
    simp [sum_simp]
    dsimp [isMem, toSumUnion, ofSumUnion, liftOfSum_ofSum]
    generalize lm1: su.right? = r?
    rcases r? with _ | ⟨r⟩
    · cases su using indInlInrOfSum
      <;> simp [sum_simp] at ⊢ lm1
      · simp [lm1]
    · cases su using indInlInrOfSum
      <;> simp [sum_simp] at ⊢ lm1
      · symm
        exact IsBiUnique.right_pred_iff_exists_left_pred_and_rel_of_rel (· ∈ sar) lm1
      · subst lm1
        rfl


instance [HasPartialCongruence rel] [∀(sal: Sαl), DecidablePred (· ∈ sal)] [∀(sar: Sαr), DecidablePred (· ∈ sar)]
         (su: SumUnion rel) (slu: SetLikeUnion rel Sαl Sαr) : Decidable (su ∈ slu) :=
         decidable_of_decidable_of_iff isMem_eq_true_iff



end SetLikeUnion


end Nemonuri.Relations.Heterogeneous

end
