module

public import Nemonuri.Relations.Heterogeneous.HContains
public import Nemonuri.Relations.Heterogeneous.IsBiUnique.SetLike
public import Nemonuri.Relations.Heterogeneous.SumRelGen.Fintype
public import Mathlib.Data.Setoid.Basic

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

--setOfLeftSet rel ↑fsL = setOfRightSet rel ↑fsR

/-
variable (rel) in
theorem
-/


variable (rel) in
theorem finsetOfLeftFinset_eq_finsetOfRightFinset_iff_setHEq [IsBiUnique rel] (fsL: Finset αl) (fsR: Finset αr)
  : (finsetOfLeftFinset rel fsL = finsetOfRightFinset rel fsR) ↔ (SetHEq rel ↑fsL ↑fsR) := by
  dsimp [setHEq_def]
  exact finsetOfLeftFinset_eq_finsetOfRightFinset_iff_setOfLeftSet_eq_setOfRightSet

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
         (slu: SetLikeUnion rel Sαl Sαr) (su: SumUnion rel) : Decidable (su ∈ slu) :=
         decidable_of_decidable_of_iff isMem_eq_true_iff


def toFinset [∀(sal: Sαl), Fintype sal] [∀(sar: Sαr), Fintype sar]
             (slu: SetLikeUnion rel Sαl Sαr) : Finset (SumUnion rel) :=
  slu.toSumUnion.funElim
    (fun (sal: Sαl) =>
      let unattach : ↑sal ↪ αl := ⟨Subtype.val, Subtype.val_injective⟩
      (Finset.univ: Finset sal).map unattach |> finsetOfLeftFinset rel )
    (fun (sar: Sαr) =>
      let unattach : ↑sar ↪ αr := ⟨Subtype.val, Subtype.val_injective⟩
      (Finset.univ: Finset sar).map unattach |> finsetOfRightFinset rel )
    (by
      intro sal sar lm1
      dsimp [finsetOfLeftFinset, finsetOfRightFinset]
      simp [Finset.ext_iff]
      simp [setLikeHEq_def, setHEq_iff_forall_iff] at lm1
      intro su
      specialize lm1 su
      conv =>
        conv => lhs; arg 1; ext; arg 2; rw [Eq.comm]
        conv => rhs; arg 1; ext; arg 2; rw [Eq.comm]
      exact lm1 )

theorem toFinset_mem_iff_self_mem [∀(sal: Sαl), Fintype sal] [∀(sar: Sαr), Fintype sar] {slu: SetLikeUnion rel Sαl Sαr} (su: SumUnion rel)
  : (su ∈ slu.toFinset) ↔ (su ∈ slu) := by
  dsimp [toFinset, toSumUnion]
  cases slu using indOfSumUnion with
  | inl sl =>
    simp [sum_simp]
    dsimp [ofSumUnion, funElim_eq_ofSum, finsetOfLeftFinset]
    simp
    conv =>
      rhs; dsimp [setOfLeftSet]
      arg 1; ext; arg 2; rw [Eq.comm]
    rfl
  | inr sr =>
    simp [sum_simp]
    dsimp [ofSumUnion, funElim_eq_ofSum, finsetOfRightFinset]
    simp
    conv =>
      rhs; dsimp [setOfRightSet]
      arg 1; ext; arg 2; rw [Eq.comm]
    rfl

instance toFintype [∀(sal: Sαl), Fintype sal] [∀(sar: Sαr), Fintype sar] (slu: SetLikeUnion rel Sαl Sαr) : Fintype ↑slu :=
  have lm1 su := (toFinset_mem_iff_self_mem su).mp
  let reattach : ↑slu.toFinset ↪ ↑slu := ⟨Subtype.map id lm1, Subtype.map_injective lm1 Function.injective_id⟩
  {
    elems := slu.toFinset.attach.map reattach
    complete := by
      subst reattach
      simp
      intro su lm2
      exists su
      simp [Subtype.map_def]
      exact (toFinset_mem_iff_self_mem su).mpr lm2
  }

protected instance fintype [DecidableEq Sαl] [DecidableEq Sαr] [DecidableRel (SetLikeHEq rel Sαl Sαr)] [Fintype Sαl] [Fintype Sαr] : Fintype (SetLikeUnion rel Sαl Sαr) :=
  inferInstanceAs (Fintype (SumUnion ((SetLikeHEq rel Sαl Sαr))))


def areEq [∀(sal: Sαl), Fintype sal] [DecidableEq αl] (sal1 sal2: Sαl) : Bool :=
  let fs1 : Finset αl := (Finset.univ: Finset sal1).map ⟨Subtype.val, Subtype.val_injective⟩
  let fs2 : Finset αl := (Finset.univ: Finset sal2).map ⟨Subtype.val, Subtype.val_injective⟩
  decide (fs1 = fs2)

theorem areEq_true_iff_eq [∀(sal: Sαl), Fintype sal] [DecidableEq αl] {sal1 sal2: Sαl}
  : (areEq sal1 sal2 = .true) ↔ (sal1 = sal2) := by
  simp [areEq, Finset.ext_iff]
  conv => rhs; simp [SetLike.ext_iff]

instance (priority := 10) [∀(sal: Sαl), Fintype sal] [DecidableEq αl] : DecidableEq Sαl :=
  fun _ _ => decidable_of_decidable_of_iff areEq_true_iff_eq


variable (rel) in
def areSetLikeHEq [DecidableRel rel] (sal: Sαl) [Fintype sal] (sar: Sαr) [Fintype sar] : Bool :=
  let fsL : Finset αl := (Finset.univ: Finset ↑sal).map ⟨Subtype.val, Subtype.val_injective⟩
  let fsR : Finset αr := (Finset.univ: Finset ↑sar).map ⟨Subtype.val, Subtype.val_injective⟩
  if fsL.val.card ≠ fsR.val.card then .false else
  Quotient.liftOn₂ fsL.val fsR.val (fun ls rs => isHSublist rel ls rs) (by
    intro ls1 rs1 ls2 rs2 lm1 lm2
    change List.Perm _ _ at lm1 lm2
    exact isHSublist_respects_perm ls1 ls2 lm1 rs1 rs2 lm2)

/-
attribute [-simp] Subtype.exists Subtype.forall in
theorem areSetLikeHEq_eq_true_iff_setlikeHEq [DecidableRel rel] (sal: Sαl) [Fintype sal] (sar: Sαr) [Fintype sar]
  : (areSetLikeHEq rel sal sar = .true) ↔ (SetLikeHEq rel Sαl Sαr sal sar) := by
  rename Fintype ↑sal => ftL
  rename Fintype ↑sar => ftR
  rcases ftL with ⟨fsL, lm1⟩
  rcases ftR with ⟨fsR, lm2⟩
  conv =>
    rhs
    dsimp [setLikeHEq_def]
-/
/-
  rcases ftL with ⟨⟨ls, lm1⟩, lm2⟩
  rcases ftR with ⟨⟨rs, lm3⟩, lm4⟩
  cases ls using Quotient.ind
  cases rs using Quotient.ind
  rename_i ls rs
  revert lm1 lm3
  simp
  intro lm1 lm2 lm3 lm4
  dsimp [areSetLikeHEq, Finset.univ]
  simp
  dsimp [isHSublist, hcontains]
  simp
  simp [setLikeHEq_def, setHEq_iff_forall_iff_imp_and_imp]
-/
/-
  constructor
  · rintro ⟨lm5, lm6⟩
    refine ⟨?_, ?_⟩
    · intro l lm7
      specialize lm6 l lm7 (lm2 l lm7)
      rcases lm6 with ⟨r, lm6, lm8⟩
      rcases lm6 with ⟨lm6, lm9⟩
      exists r
    · intro r lm7
      by_contra lm8
      simp at lm8
      revert lm6
      simp
      rcases ls with _ | ⟨l, ls⟩
      · rewrite [Eq.comm] at lm5
        simp at lm5
        subst lm5
        specialize lm4 r lm7
        simp at lm4
      ·
-/
/-
      have lm9 : ls ≠ [] := by
        intro lm9_1
        subst lm9_1
        rewrite [Eq.comm] at lm5
        simp at lm5
        subst lm5
        specialize lm4 r lm7
        simp at lm4
      let l := ls.head lm9
      exists l
      simp
      refine ⟨?_, ?_⟩
      · subst l; exact List.head_mem lm9
      · intro r2 lm10 lm11 lm12
        specialize lm8 l.val l.property
        subst l
      --intro r2 lm10 lm11 lm12
-/
/-
      by_cases lm8: ∃l ∈ ls, rel l.val r
      · rcases lm8 with ⟨⟨l, lm8⟩, lm9, lm10⟩
        dsimp at lm10
        specialize lm6 l lm8 lm9
        exists l
      · simp at lm8
        have lm9 : ls ≠ [] := by
          intro lm9_1
          subst lm9_1
          rewrite [Eq.comm] at lm5
          simp at lm5
          subst lm5
          simp at lm4
        rcases ls.head lm9 with ⟨l, lm10⟩
        specialize lm6 l lm10 (lm2 l lm10)
        rcases lm6 with ⟨r2, ⟨lm11, lm12⟩, lm13⟩
-/



/-
      have lm8 : ls ≠ [] := by
        intro lm8_1
        subst lm8_1
        rewrite [Eq.comm] at lm5
        simp at lm5
        subst lm5
        simp at lm4
      rcases lm9: ls.head lm8 with ⟨l, lm10⟩
      exists l
      specialize lm6 l lm10
      simp [← lm9] at lm6
      rcases lm6 with ⟨r2, ⟨lm6, lm12⟩, lm11⟩
-/
/-
      rcases rs with _ | ⟨r, rs⟩
      · simp at lm4
      · rcases ls with _ | ⟨l, ls⟩
        · simp at lm5
        · simp at lm3 lm4 lm1 lm2 lm5 lm6
          rcases l with ⟨l, lm8⟩
          rcases r with ⟨r, lm9⟩
          simp at lm4 lm6
          specialize lm6 l lm8
          simp at lm6
          rcases lm6 with ⟨r2, ⟨lm6, lm10⟩, lm11⟩
-/
/-
          rcases lm4 with lm4 | lm4
          · rw [Eq.comm] at lm4
            subst lm4
            simp at lm6
-/
      --by_contra lm8
      --simp at lm8



--def hcontains (l: )

/-
variable (rel) in
def areSetLikeHEqAux [DecidableRel rel] {sal: Sαl} [Fintype sal] {sar: Sαr} [Fintype sar] (ls: List ↑sal) : (List ↑sar) → Bool
  | [] => .true
  | r::rs => ls.any (fun l => decide (rel l.val r.val)) && areSetLikeHEqAux ls rs
-/

/-
attribute [-simp] Subtype.exists Subtype.forall in
theorem areSetLikeHEqAux_perm_cons [DecidableRel rel] {sal: Sαl} [Fintype sal] {sar: Sαr} [Fintype sar]
  (ls1 ls2: List ↑sal) (req1: ls1.Perm ls2) (rs1 rs2: List ↑sar) (req2: rs1.Perm rs2)
  (req3: areSetLikeHEqAux rel ls1 rs1 = areSetLikeHEqAux rel ls2 rs2) (l: ↑sal)
  : areSetLikeHEqAux rel (l :: ls1) rs1 = areSetLikeHEqAux rel (l :: ls2) rs2 := by
  cases req2 with
  | nil => dsimp [areSetLikeHEqAux]
  | @cons r rs1 rs2 lm1 =>
    rewrite [Bool.eq_iff_iff] at req3 ⊢
    simp [areSetLikeHEqAux, req1.mem_iff] at req3 ⊢
    intro lm2
    by_cases lm3: ∃ x ∈ ls2, rel ↑x ↑r
    · clear lm2
      rcases lm3 with ⟨l2, lm3, lm4⟩
      specialize req3 l2 lm3 lm4
      exact areSetLikeHEqAux_perm_cons ls1 ls2 req1 rs1 rs2 lm1 req3 l
    · simp [lm3] at lm2
      simp at lm3
      specialize lm3 l
      simp [lm2] at lm3
-/
    --by_cases lm3: l ∈ ls2
    --·

/-
    by_cases lm2: l ∈ ls1 ∧ rel l.val r.val
    · have lm3 : ∃x ∈ ls1, rel ↑x ↑r := by exists l
      simp [lm3] at ⊢ req3
      rcases lm2 with ⟨lm2, lm4⟩
      simp [lm4]
      simp only [req1.mem_iff] at lm3
      simp [lm3] at req3
      exact areSetLikeHEqAux_perm_cons ls1 ls2 req1 rs1 rs2 lm1 req3 l
    · rewrite [and_comm] at lm2
      simp at lm2
      by_cases lm3: rel l.val r.val
      · specialize lm2 lm3
        simp [lm3]
        have lm4 : ¬∃ x ∈ ls1, rel ↑x ↑r := by
          simp
          intro l2 lm4_1 lm4_2
          have lm4_3 := IsBiUnique.leftUnique lm3 lm4_2
          simp at lm4_3
          subst lm4_3
          contradiction
        simp [lm4] at req3
-/

/-
attribute [-simp] Subtype.exists Subtype.forall in
theorem areSetLikeHEqAux_respects_perm [DecidableRel rel] {sal: Sαl} [Fintype sal] {sar: Sαr} [Fintype sar]
  (ls1 ls2: List ↑sal) (req1: ls1.Perm ls2) (rs1 rs2: List ↑sar) (req2: rs1.Perm rs2)
  : areSetLikeHEqAux rel ls1 rs1 = areSetLikeHEqAux rel ls2 rs2 := by
  cases req1 with
  | nil =>
    induction req2 <;> try simp [areSetLikeHEqAux]
    case trans lm1 lm2 => exact lm1.trans lm2
  | @cons l ls1 ls2 lm1 =>
    have lm2 : (l :: ls1).Perm (l :: ls2) := by simpa only [List.perm_cons] using lm1
    cases req2 with
    | nil => dsimp [areSetLikeHEqAux]
    | @cons r rs1 rs2 lm3 =>
      dsimp [areSetLikeHEqAux]
      have lm4 := areSetLikeHEqAux_respects_perm (l :: ls1) (l :: ls2) lm2 rs1 rs2 lm3
      rw [lm4, Bool.eq_iff_iff]
      simp
      intro _
      simp only [lm1.mem_iff]
    | swap r1 r2 rs =>
      rw [Bool.eq_iff_iff]
      simp [areSetLikeHEqAux]
      conv => lhs; rw [and_left_comm]
      simp [lm1.mem_iff]
      intro _ _
      exact areSetLikeHEqAux_respects_perm (l :: ls1) (l :: ls2) lm2 rs rs List.Perm.rfl
    | trans lm3 lm4 =>
      rename_i rs3
      rcases rs1 with _ | ⟨r1, rs1⟩
      <;> rcases rs2 with _ | ⟨r2, rs2⟩
      <;> rcases rs3 with _ | ⟨r3, rs3⟩
      <;> try simp at lm3 lm4
      · dsimp [areSetLikeHEqAux]
      · dsimp [areSetLikeHEqAux]
        rw [Bool.eq_iff_iff]
        simp
-/
/-
      rename_i rs3
      have lm5 := areSetLikeHEqAux_respects_perm _ _ lm2 rs1 rs3 lm3
      have lm6 := areSetLikeHEqAux_respects_perm _ _ lm2 rs3 rs2 lm4
-/
      --have lm7 := lm5.trans lm6

/-
      rw [lm7]
      rcases rs2 with _ | ⟨r, rs⟩
      · dsimp [areSetLikeHEqAux]
      · dsimp [areSetLikeHEqAux]
        rw [Bool.eq_iff_iff]
        simp [lm1.mem_iff]
        intro _
        exact areSetLikeHEqAux_respects_perm _ _ lm2 rs rs List.Perm.rfl
-/
/-
    rcases rs1 with _ | ⟨r1, rs1⟩
    <;> rcases rs2 with _ | ⟨r2, rs2⟩
    <;> try simp at req2
    · dsimp [areSetLikeHEqAux]
    · rw [Bool.eq_iff_iff]
      simp [areSetLikeHEqAux]
      by_cases lm3: r1 = r2
      · subst lm3
        simp [lm1.mem_iff]
        intro lm3
        simp at req2
        exact areSetLikeHEqAux_respects_perm _ _ lm2 rs1 rs2 req2
      · simp [lm1.mem_iff]
        by_cases lm4: rel l.val r1.val
        · simp [lm4]
          have lm5 := (IsBiUnique.right_ne_iff_not_rel lm4 r2.val).mp ?h1
          case h1 => simpa using lm3
          simp [lm5]
-/

/-
    · cases req2 with
      | nil => dsimp [areSetLikeHEqAux]
      | trans lm1 lm2 =>
        simp at lm1
        subst lm1
        simp at lm2
        subst lm2
        dsimp [areSetLikeHEqAux]
    · cases req2 with
      | @cons _ _ rs2 lm3 =>
        dsimp [areSetLikeHEqAux]
        have lm4 := areSetLikeHEqAux_respects_perm (l :: ls1) (l :: ls2) lm2 rs1 rs2 lm3
        rw [lm4, Bool.eq_iff_iff]
        simp
        intro _
        simp only [lm1.mem_iff]
      | swap r2 _ rs =>
        rw [Bool.eq_iff_iff]
        simp [areSetLikeHEqAux]
        conv => lhs; rw [and_left_comm]
        simp [lm1.mem_iff]
        intro _ _
        exact areSetLikeHEqAux_respects_perm (l :: ls1) (l :: ls2) lm2 rs rs List.Perm.rfl
      | trans lm3 lm4 =>
        have lm5 := lm3.trans lm4
-/

/-
    cases req2 with
    | nil => dsimp [areSetLikeHEqAux]
    | @cons r rs1 rs2 lm3 =>
      dsimp [areSetLikeHEqAux]
      have lm4 := areSetLikeHEqAux_respects_perm (l :: ls1) (l :: ls2) lm2 rs1 rs2 lm3
      rw [lm4, Bool.eq_iff_iff]
      simp
      intro _
      simp only [lm1.mem_iff]
    | swap r1 r2 rs =>
      rw [Bool.eq_iff_iff]
      simp [areSetLikeHEqAux]
      conv => lhs; rw [and_left_comm]
      simp [lm1.mem_iff]
      intro _ _
      exact areSetLikeHEqAux_respects_perm (l :: ls1) (l :: ls2) lm2 rs rs List.Perm.rfl
    | trans lm3 lm4 =>
      rename_i rs3
      have lm5 := areSetLikeHEqAux_respects_perm _ _ lm2 rs1 rs3 lm3
      have lm6 := areSetLikeHEqAux_respects_perm _ _ lm2.symm rs3 rs2 lm4
      have lm7 := lm5.trans lm6
      rw [lm7]
      rcases rs2 with _ | ⟨r, rs⟩
      · dsimp [areSetLikeHEqAux]
      · dsimp [areSetLikeHEqAux]
        rw [Bool.eq_iff_iff]
        simp [lm1.mem_iff]
        intro _
        exact areSetLikeHEqAux_respects_perm _ _ lm2 rs rs List.Perm.rfl
-/

  --| swap l1 l2 ls =>
    --have lm1 : (l2 :: l1 :: ls).Perm (l1 :: l2 :: ls) := List.Perm.swap l1 l2 ls


/-
attribute [-simp] Subtype.exists Subtype.forall in
variable (rel) in
def areSetLikeHEq [DecidableRel rel] (sal: Sαl) [Fintype sal] (sar: Sαr) [Fintype sar] : Bool :=
  let fsL : Finset ↑sal := Finset.univ
  let fsR : Finset ↑sar := Finset.univ
  if fsL.val.card ≠ fsR.val.card then .false else
  Quotient.liftOn₂ fsL.val fsR.val (areSetLikeHEqAux rel) (by
    intro ls1 rs1 ls2 rs2 lm1 lm2
    change List.Perm _ _ at lm1 lm2
    induction lm1 with
    | nil =>
      induction lm2 <;> try simp [areSetLikeHEqAux]
      case trans lm1 lm2 => exact lm1.trans lm2
    | @cons l ls1 ls2 lm1 lm3 =>
  )
-/

/-
variable (rel) in
def areSetLikeHEqAux [DecidableRel rel] {sal: Sαl} [Fintype sal] {sar: Sαr} [Fintype sar] : (List ↑sal) → (List ↑sar) → Bool
  | [], [] => .true
  | l::ls, r::rs => decide (rel l.val r.val) && areSetLikeHEqAux ls rs
  | _, _ => .false


variable (rel) in
def areSetLikeHEq [DecidableRel rel] (sal: Sαl) [Fintype sal] (sar: Sαr) [Fintype sar] : Bool :=
  let listFun (x1: { x: List ↑sal // x.Nodup }) (x2: { x: List ↑sar // x.Nodup }) : Bool := areSetLikeHEqAux rel x1.val x2.val
  let fsL : Finset ↑sal := Finset.univ
  let fsR : Finset ↑sar := Finset.univ
  let ⟨msL, lm1⟩ := fsL
  let listFun' := Quotient.pliftOn msL (fun ls h => listFun ⟨ls, (by cases msL using Quotient.ind; rewrite [h] at lm1; simp at lm1; exact lm1)⟩) (by
    intro ls1 ls2 lm2 lm3 lm4
    subst lm2
    have lm5 : ls1.Nodup := lm1
    have lm6 : ls2.Nodup := by rewrite [lm3] at lm1; dsimp at lm1; exact lm1
    simp at lm3
    change List.Perm ls1 ls2 at lm4
    subst listFun
    simp [funext_iff]
    intro rs lm7
    induction lm4 with
    | nil => rfl
    | cons l lm10 lm4 =>
      simp at lm5 lm6 lm4
      rcases lm5 with ⟨lm5, lm8⟩
      rcases lm6 with ⟨lm6, lm9⟩
      specialize lm4 lm8 ?h1 lm8 lm9
      case h1 =>
        refine Multiset.coe_eq_coe.mpr ?_
        exact lm10
      induction rs with
      | nil => dsimp [areSetLikeHEqAux]
      | cons r rs lm10 =>
        dsimp [areSetLikeHEqAux]
        rewrite [Bool.eq_iff_iff]
        simp at lm7
        rcases lm7 with ⟨lm7, lm11⟩
        simp
        intro lm12
        specialize lm10 lm11
  )
-/
/-
      induction rs with
      | nil => dsimp [areSetLikeHEqAux]
      | cons r rs lm10 =>
        dsimp [areSetLikeHEqAux]
        rewrite [Bool.eq_iff_iff]
        simp at lm7
        rcases lm7 with ⟨lm7, lm11⟩
        simp
        intro lm12
-/





  --let listFun' := Quotient.pliftOn fsL.val
/-
  let setoL : Setoid ({ x: List ↑sal // x.Nodup }) := Setoid.comap Subtype.val (List.isSetoid ↑sal)
  let setoR : Setoid ({ x: List ↑sar // x.Nodup }) := Setoid.comap Subtype.val (List.isSetoid ↑sal)
  let qL : Quotient setoL :=
-/
  --if fsL.val.card ≠ fsR.val.card then .false else




/-
  Quotient.liftOn₂ fsL.val fsR.val (areSetLikeHEqAux rel) (by
    intro ls1 rs1 ls2 rs2 lm1 lm2
    change List.Perm _ _ at lm1 lm2
    induction lm1 with
    | nil =>
      induction lm2 <;> (try dsimp [areSetLikeHEqAux])
      case trans lm1 lm2 => exact lm1.trans lm2
    | cons l _ lm1 =>
      induction lm2 with
      | nil => dsimp [areSetLikeHEqAux]
      | cons r _ lm2 =>
        dsimp [areSetLikeHEqAux]
        rw [Bool.eq_iff_iff]
        simp
        intro lm3
-/




end SetLikeUnion


end Nemonuri.Relations.Heterogeneous

end
