module

public import Nemonuri.Executions.Basic
public import Nemonuri.TransitionSystem.Step
public import Mathlib.Data.Seq.Defs

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

structure IsFiniteExecutionFragment {ts: TransitionSystem} (sp: SequenceProd ts.S ts.Act) : Prop extends toBasic: IsExecutionFragment sp where
  finite: toBasic.wShape.toFiniteLabel = .finite


namespace IsFiniteExecutionFragment

variable {ts: TransitionSystem} {sp: SequenceProd ts.S ts.Act}

theorem fst_finite (h: IsFiniteExecutionFragment sp) : sp.fst.toFiniteLabel = .finite := sp.fst_toFiniteLabel_eq_of_toFiniteLabel_eq _ h.finite

theorem snd_finite (h: IsFiniteExecutionFragment sp) : sp.snd.toFiniteLabel = .finite := sp.snd_toFiniteLabel_eq_of_toFiniteLabel_eq _ h.finite

end IsFiniteExecutionFragment

@[ext (flat := false)]
structure FiniteExecutionFragment (ts: TransitionSystem) extends toSequenceProd: SequenceProd ts.S ts.Act where
  valid: IsFiniteExecutionFragment toSequenceProd

namespace FiniteExecutionFragment

open SequenceProd

variable {ts: TransitionSystem}

def minLength (fef: FiniteExecutionFragment ts) : ℕ := fef.toSequenceProd.minLength _ fef.valid.finite

@[defeq]
theorem minLength_def {fef: FiniteExecutionFragment ts} : fef.minLength = fef.toSequenceProd.minLength _ fef.valid.finite := rfl

theorem minLength?_eq_natCast_minLength {fef: FiniteExecutionFragment ts} : fef.minLength? = ↑fef.minLength := by
  dsimp [minLength_def]
  rw [← fef.toSequenceProd.minLength?_eq_natCast_minLength]

theorem minLength_eq_snd_length (fef: FiniteExecutionFragment ts) : fef.minLength = fef.snd.length fef.valid.snd_finite := by
  rcases fef with ⟨sp, lm1⟩
  dsimp [minLength_def]
  rw [← ENat.coe_inj, ← sp.minLength?_eq_natCast_minLength, ← sp.snd.length?_eq_natCast_length]
  exact lm1.wShape.minLength?_eq_snd_length?

theorem minLength_add_one_eq_fst_length (fef: FiniteExecutionFragment ts) : (fef.minLength + 1) = fef.fst.length fef.valid.fst_finite := by
  rcases fef with ⟨sp, lm1⟩
  dsimp [minLength_def]
  rw [← ENat.coe_inj, ENat.coe_add, ← sp.minLength?_eq_natCast_minLength, ← sp.fst.length?_eq_natCast_length]
  exact lm1.wShape.minLength?_add_one_eq_fst_length?

theorem fst_length?_eq_fst_length_natCast (fef: FiniteExecutionFragment ts) : fef.fst.length? = ↑(fef.fst.length (fef.toSequenceProd.fst_toFiniteLabel_eq_of_toFiniteLabel_eq _ fef.valid.finite)) :=
  fef.fst.length?_eq_natCast_length _

theorem snd_length?_eq_snd_length_natCast (fef: FiniteExecutionFragment ts) : fef.snd.length? = ↑(fef.snd.length (fef.toSequenceProd.snd_toFiniteLabel_eq_of_toFiniteLabel_eq _ fef.valid.finite)) :=
  fef.snd.length?_eq_natCast_length _

theorem minLength_sub_natCast_lt_fst_length? (fef: FiniteExecutionFragment ts) (subN: ℕ) : ↑(fef.minLength - subN) < fef.fst.length? := by
  rw [fef.fst_length?_eq_fst_length_natCast, ENat.coe_lt_coe, ← fef.minLength_add_one_eq_fst_length]
  simp

theorem minLength_natCast_lt_fst_length? (fef: FiniteExecutionFragment ts) : (↑fef.minLength: ℕ∞) < fef.fst.length? := fef.minLength_sub_natCast_lt_fst_length? 0

theorem natCast_lt_fst_length?_of_le_minLength (fef: FiniteExecutionFragment ts) (i: ℕ) (req: i ≤ fef.minLength) : (↑i: ℕ∞) < fef.fst.length? :=
  calc
    (↑i: ℕ∞) ≤ _ := ENat.coe_le_coe.mpr req
    _ < _ := fef.minLength_natCast_lt_fst_length?

theorem minLength_sub_one_natCast_lt_snd_length?_of_lt (fef: FiniteExecutionFragment ts) {n: ℕ} (req: n < fef.minLength) : (↑(fef.minLength - 1): ℕ∞) < fef.snd.length? := by
  rw [fef.snd_length?_eq_snd_length_natCast, ENat.coe_lt_coe, ← fef.minLength_eq_snd_length]
  exact Nat.sub_one_lt_of_lt req


def lastState (fef: FiniteExecutionFragment ts) : ts.S := fef.valid.wShape.lastFst fef.valid.finite


instance : WellFoundedRelation (FiniteExecutionFragment ts) := invImage FiniteExecutionFragment.minLength inferInstance


def initOf (ts: TransitionSystem) (s: ts.S) : FiniteExecutionFragment ts where
  toSequenceProd := .singleFst ts.S ts.Act s
  valid := by
    have lm1 : (singleFst ts.S ts.Act s).IsWShape := .of_singleFst
    refine ⟨⟨lm1, ?_⟩, ?_⟩
    · intro _ lm2
      dsimp [singleFst, Sequence.nil_length?_eq_zero] at lm2
      simp at lm2
    · refine lm1.finite_iff_snd_finite.mpr ?_
      dsimp [singleFst]
      refine Sequence.finite_of_empty ?_
      exact Sequence.nil_empty

theorem initOf_minLength (s: ts.S) : (initOf ts s).minLength = 0 := by
  rw [← ENat.coe_inj, ← minLength?_eq_natCast_minLength]
  dsimp [initOf]
  have lm1 : (singleFst ts.S ts.Act s).IsWShape := .of_singleFst
  rw [lm1.minLength?_eq_snd_length?]
  dsimp [singleFst]
  exact Sequence.nil_length?_eq_zero


def step (fef: FiniteExecutionFragment ts) (ste: StepR ts fef.lastState) : FiniteExecutionFragment ts where
  toSequenceProd := fef.toSequenceProd.stepR ste.post ste.act
  valid := by
    generalize lm1: fef.toSequenceProd.stepR ste.post ste.act = sp
    have lm2 : IsWShape sp := by
      rw [← lm1]
      exact .stepR_isWShape fef.valid.wShape _ _
    have lm3 : sp.minLength? = ↑(fef.minLength + 1) := by
      rw [lm2.minLength?_eq_snd_length?, ← lm1]
      dsimp [SequenceProd.stepR, Sequence.snoc]
      simp
      rw [← fef.minLength?_eq_natCast_minLength, fef.valid.wShape.minLength?_eq_snd_length?]
    have lm4 : lm2.toFiniteLabel = .finite := lm2.finite_of_minLength?_eq_natCast _ lm3
    refine ⟨⟨lm2, ?_⟩, lm4⟩
    intro i lm5
    rewrite [← lm2.minLength?_eq_snd_length?, lm3, ENat.coe_lt_coe] at lm5
    simp at lm5
    have lm7 := ste.valid
    simp [← lm1, SequenceProd.stepR]
    rcases eq_or_lt_of_le lm5 with lm6 | lm6
    · subst lm6
      have lm6 : ↑fef.minLength < fef.fst.length? := by rw [← fef.valid.wShape.minLength?_add_one_eq_fst_length?, fef.minLength?_eq_natCast_minLength, ENat.lt_coe_add_one_iff]
      have lm8 : fef.snd.length? = ↑fef.minLength := by
        rw [← fef.minLength?_eq_natCast_minLength]
        exact fef.valid.wShape.minLength?_eq_snd_length?.symm
      have lm9 : fef.fst.length? = ↑(fef.minLength + 1) := by
        rw [fef.valid.wShape.length?_eq, lm8]
        simp
      rewrite [(fef.fst.snoc_getAt_eq_getAt _ lm6 ste.post),
               (fef.snd.snoc_getAt_eq_of_length_eq_natCast _ lm8 _),
               (fef.fst.snoc_getAt_eq_of_length_eq_natCast (_ + 1) lm9 _)]
      dsimp [lastState, IsWShape.lastFst] at lm7
      simp [Sequence.last_eq_getAt] at lm7
      have lm10 : fef.fst.length (fef.valid.wShape.finite_iff_fst_finite.mp fef.valid.finite) - 1 = fef.minLength := by
        have lm10_1 := fef.fst.length_eq_of_length?_eq_natCast lm9
        simp [lm10_1]
      simp [lm10] at lm7
      exact lm7
    · have lm8 := fef.valid.lts_tr
      have lm9 := ENat.coe_lt_coe.mpr lm6
      rw [← fef.minLength?_eq_natCast_minLength, fef.valid.wShape.minLength?_eq_snd_length?] at lm9
      specialize lm8 i lm9
      have lm10 := Nat.succ_lt_succ lm6 |> ENat.coe_lt_coe.mpr
      dsimp at lm10
      conv at lm10 =>
        rhs
        rw [ENat.coe_add, ← fef.minLength?_eq_natCast_minLength, ENat.coe_one, fef.valid.wShape.minLength?_add_one_eq_fst_length?]
      have lm11 : ↑i < fef.fst.length? := calc
        (↑i: ℕ∞) < ↑(i + 1) := by rw [ENat.coe_lt_coe]; simp
        _ < _ := lm10
      rewrite [(fef.fst.snoc_getAt_eq_getAt i lm11 _),
               (fef.snd.snoc_getAt_eq_getAt i lm9 _),
               (fef.fst.snoc_getAt_eq_getAt (i+1) lm10 _)]
      exact lm8

theorem step_minLength (fef: FiniteExecutionFragment ts) (ste: StepR ts fef.lastState) : (fef.step ste).minLength = fef.minLength + 1 := by
  simp only [minLength_eq_snd_length]
  rw [← ENat.coe_inj]
  simp [← Sequence.length?_eq_natCast_length]
  dsimp [step, SequenceProd.stepR, Sequence.snoc]

theorem step_ne_self (fef: FiniteExecutionFragment ts) (ste: StepR ts fef.lastState) : fef.step ste ≠ fef := by
  intro lm1
  replace lm1 := congrArg minLength lm1
  rewrite [fef.step_minLength ste] at lm1
  simp at lm1


def dropLastStep (fef: FiniteExecutionFragment ts) : FiniteExecutionFragment ts where
  toSequenceProd :=
    match fef.minLength with
    | 0 => fef.toSequenceProd
    | ml + 1 => fef.dropLast
  valid := by
    generalize lm1: fef.minLength = ml
    rcases ml with _ | ⟨ml⟩
    · simp
      exact fef.valid
    · simp
      have lm2 : IsWShape fef.dropLast := by
        refine .dropLast_isWShape_of_minLength?_post fef.valid.wShape ?_
        rw [fef.minLength?_eq_natCast_minLength, lm1]
        simp
      have lm3 : fef.dropLast.minLength? = ↑ml := by
        rw [lm2.minLength?_eq_snd_length?]
        dsimp [dropLast, Sequence.dropLast]
        rw [← ENat.coe_inj, ← fef.minLength?_eq_natCast_minLength, fef.valid.wShape.minLength?_eq_snd_length?] at lm1
        rw [lm1, ← ENat.coe_one, ← ENat.coe_sub]
        simp
      have lm4 : lm2.toFiniteLabel = .finite := lm2.finite_of_minLength?_eq_natCast ml lm3
      refine ⟨⟨lm2, ?_⟩, lm4⟩
      intro i lm5
      have lm6 := fef.valid.lts_tr
      have lm7 : ↑i < fef.snd.length? := by
        rewrite [← ENat.coe_inj, ← fef.minLength?_eq_natCast_minLength, fef.valid.wShape.minLength?_eq_snd_length?] at lm1
        rewrite [lm2.minLength?_eq_snd_length?] at lm3
        calc
          ↑i < _ := lm5
          _ < fef.snd.length? := by rw [lm3, lm1]; simp [ENat.lt_coe_add_one_iff]
      specialize lm6 i lm7
      dsimp [dropLast, Sequence]
      simp [Sequence.dropLast_getAt_eq_getAt]
      exact lm6

theorem dropLastStep_lastState_of_minLength_eq_zero (fef: FiniteExecutionFragment ts) (req: fef.minLength = 0)
  : fef.dropLastStep.lastState = fef.lastState := by
  dsimp [dropLastStep]
  simp [req]

theorem dropLastSteq_lastState_of_minLength_pos (fef: FiniteExecutionFragment ts) (req: 0 < fef.minLength)
  : fef.dropLastStep.lastState = fef.fst.getAt (fef.minLength - 1) (fef.minLength_sub_natCast_lt_fst_length? 1) := by
  rw [← Option.some_inj, ← fef.fst.getAt?_eq_some_getAt]
  generalize lm1: fef.minLength = ml at ⊢ req
  rcases ml with _ | ⟨ml⟩
  · simp at req
  · dsimp [lastState, IsWShape.lastFst, dropLastStep]
    simp [lm1]
    have lm2 : ↑ml < fef.fst.length? := by
      have lm2_1 : ml < ml + 1 + 1 := by simp
      rw [← lm1, fef.minLength_add_one_eq_fst_length, ← ENat.coe_lt_coe, ← fef.fst.length?_eq_natCast_length] at lm2_1
      exact lm2_1
    rw [fef.fst.getAt?_eq_some_getAt lm2, Option.some_inj]
    dsimp [dropLast]
    rw [Sequence.last_eq_getAt]
    have lm3 := fef.minLength_add_one_eq_fst_length
    have lm4 := fef.fst.dropLast_getAt_eq_getAt ml ?h1
    case h1 =>
      dsimp [Sequence.dropLast]
      rw [(fef.fst.length?_eq_natCast_length fef.valid.fst_finite), ← lm3, lm1,
          ← ENat.coe_one, ← ENat.coe_sub, ENat.coe_lt_coe]
      simp
    rw [← lm4]
    congr
    rw [← ENat.coe_inj, ENat.coe_sub, ← Sequence.length?_eq_natCast_length]
    dsimp [Sequence.dropLast]
    rw [(fef.fst.length?_eq_natCast_length fef.valid.fst_finite), ← lm3, lm1,
        ← ENat.coe_one, ← ENat.coe_sub, ← ENat.coe_sub, ENat.coe_inj]
    dsimp


/-
def lastStep (fef: FiniteExecutionFragment ts) (req: 0 < fef.minLength) : StepR ts (fef.dropLastStep.lastState) :=
  let v := fef.valid.wShape.last (by rw [fef.minLength?_eq_natCast_minLength]; simpa using req) fef.valid.finite
  {
    act := v.snd
    post := v.fst
    valid := by
      subst v
      rcases lm1: fef.minLength with _ | ⟨ml⟩
      · simp [lm1] at req
      · dsimp [dropLastStep, lastState, IsWShape.lastFst, IsWShape.last]
        simp [lm1]
        have := last_eqgetat
  }
-/




def lastStep (fef: FiniteExecutionFragment ts) (req: 0 < fef.minLength) : Step ts where
  pre := fef.fst.getAt (fef.minLength - 1) (by
    rw [fef.fst_length?_eq_fst_length_natCast, ENat.coe_lt_coe, ← fef.minLength_add_one_eq_fst_length]; simp)
  act := fef.snd.getAt (fef.minLength - 1) (by
    rw [fef.snd_length?_eq_snd_length_natCast, ENat.coe_lt_coe, ← fef.minLength_eq_snd_length]
    refine Nat.sub_one_lt ?_
    intro lm1; simp [lm1] at req )
  post := fef.fst.getAt fef.minLength (by
    rw [fef.fst_length?_eq_fst_length_natCast, ENat.coe_lt_coe, ← fef.minLength_add_one_eq_fst_length]; simp)
  valid := by
    have lm1 := fef.valid.lts_tr (fef.minLength - 1)
    conv at lm1 =>
      arg -2
      rw [fef.snd_length?_eq_snd_length_natCast, ENat.coe_lt_coe, ← fef.minLength_eq_snd_length]
    simp [req] at lm1
    have lm2 : fef.minLength - 1 + 1 = fef.minLength := by omega
    simp [lm2] at lm1
    exact lm1


theorem lastStep_pre_eq_dropLastStep_lastState (fef: FiniteExecutionFragment ts) (req: 0 < fef.minLength)
  : (fef.lastStep req).pre = fef.dropLastStep.lastState := by
  rw [fef.dropLastSteq_lastState_of_minLength_pos req]
  dsimp [lastStep]


def lastStepR (fef: FiniteExecutionFragment ts) (req: 0 < fef.minLength) : StepR ts fef.dropLastStep.lastState :=
  let st := fef.lastStep req
  {
    act := st.act
    post := st.post
    valid := by
      have lm1 := fef.lastStep_pre_eq_dropLastStep_lastState req
      have lm2 := st.valid
      subst st
      rw [← lm1]
      exact lm2
  }

@[elab_as_elim]
def recInitStep.{um}
  {motive: (FiniteExecutionFragment ts) → Sort um}
  (init: (s: ts.S) → motive (.initOf ts s))
  (step: (fef: FiniteExecutionFragment ts) → (ste: StepR ts fef.lastState) → motive fef → (motive (.step fef ste)))
  (t: FiniteExecutionFragment ts)
  : motive t :=
  match h1: t.minLength with
  | 0 => init t.lastState |> cast (by
      congr
      have lm1 := h1
      dsimp [minLength] at lm1
      rewrite [← ENat.coe_inj, ← SequenceProd.minLength?_eq_natCast_minLength] at lm1
      have lm2 := t.valid.wShape.singleFst_eq_self_of_minLength?_eq_zero lm1
      refine FiniteExecutionFragment.ext ?_
      dsimp [initOf, lastState]
      refine Eq.trans ?_ lm2
      congr
      symm
      exact t.valid.wShape.headFst_eq_lastFst_of_minLength?_eq_zero lm1 )
  | ml + 1 =>
    have lm1 : 0 < t.minLength := by rw [h1]; simp
    let fef := t.dropLastStep
    let ste := t.lastStepR lm1
    step fef ste (recInitStep init step fef) |> cast (by
      congr
      subst fef ste
      refine FiniteExecutionFragment.ext ?_
      dsimp [FiniteExecutionFragment.step, lastStepR, lastStep, dropLastStep]
      simp [h1]
      have lm2 := ENat.coe_lt_coe.mpr lm1
      rw [← t.minLength?_eq_natCast_minLength] at lm2
      rcases t.nonempty_of_minLength?_pos lm2 with ⟨lm3, lm4⟩
      have lm5 := t.toSequenceProd.last_dropLast_stepR_eq_self _ t.valid.finite _ lm4
      dsimp at lm5
      refine Eq.trans ?_ lm5
      congr
      · dsimp [last]
        rw [t.fst.last_eq_getAt]
        congr
        rw [← t.minLength_add_one_eq_fst_length, h1]
        dsimp
      · dsimp [last]
        rw [t.snd.last_eq_getAt]
        congr
        rw [← t.minLength_eq_snd_length, h1]
        dsimp )
  termination_by t
  decreasing_by
    generalize lm2: t.minLength = ml
    rw [lm2] at lm1
    rcases ml with _ | ⟨ml⟩
    · simp at lm1
    · dsimp [dropLastStep]
      simp [lm2]
      dsimp [minLength]
      rw [← ENat.coe_le_coe, ← SequenceProd.minLength?_eq_natCast_minLength]
      rename_i lm3
      rewrite [← ENat.coe_lt_coe, ← minLength?_eq_natCast_minLength] at lm3
      have lm4 := t.valid.wShape.dropLast_isWShape_of_minLength?_post lm3
      have lm5 := congrArg (· + 1) lm2
      rewrite [t.minLength_add_one_eq_fst_length, ← ENat.coe_inj, ← t.fst.length?_eq_natCast_length] at lm5
      refine @ENat.add_le_add_iff_right _ _ 1 ?_ |>.mp ?_
      · simp
      · rw [lm4.minLength?_add_one_eq_fst_length?]
        dsimp [dropLast, Sequence.dropLast]
        rw [lm5]
        simp




def stepAt? (fef: FiniteExecutionFragment ts) (i: ℕ) : Option (Step ts) :=
  if h1: fef.minLength ≤ i then .none else
  have lm1 : i < fef.minLength := by simpa using h1
  .some {
    pre := fef.fst.getAt i (by
      rw [fef.fst.length?_eq_natCast_length fef.valid.fst_finite, ENat.coe_lt_coe, ← fef.minLength_add_one_eq_fst_length]
      calc
        i < _ := lm1
        _ < _ := Nat.lt_add_one _  )
    act := fef.snd.getAt i (by
      rw [fef.snd.length?_eq_natCast_length fef.valid.snd_finite, ENat.coe_lt_coe, ← fef.minLength_eq_snd_length]
      exact lm1 )
    post := fef.fst.getAt (i + 1) (by
      rw [fef.fst.length?_eq_natCast_length fef.valid.fst_finite, ENat.coe_lt_coe, ← fef.minLength_add_one_eq_fst_length]
      simpa using lm1 )
    valid := fef.valid.lts_tr i _ }


theorem stepAt?_isStreamSeq (fef: FiniteExecutionFragment ts) : Stream'.IsSeq (fef.stepAt?) := by
  intro i
  simp [stepAt?]
  intro lm1
  calc
    _ ≤ _ := lm1
    _ ≤ i + 1 := Nat.le_add_right _ _

def stepAtStreamSeq (fef: FiniteExecutionFragment ts) : Stream'.Seq (Step ts) := ⟨fef.stepAt?, fef.stepAt?_isStreamSeq⟩

theorem stepAt?_eq_none_iff (fef: FiniteExecutionFragment ts) (i: ℕ) : (fef.stepAt? i = .none) ↔ (fef.minLength ≤ i) := by
  dsimp [stepAt?]
  simp


end FiniteExecutionFragment

end Nemonuri.TransitionSystem

end
