module

public import Nemonuri.Executions.Basic
public import Nemonuri.TransitionSystem.Step

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

structure IsFiniteExecutionFragment {ts: TransitionSystem} (sp: SequenceProd ts.S ts.Act) : Prop extends toBasic: IsExecutionFragment sp where
  finite: toBasic.wShape.toFiniteLabel = .finite


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

theorem minLength_eq_snd_length (fef: FiniteExecutionFragment ts) : fef.minLength = fef.snd.length (fef.toSequenceProd.snd_toFiniteLabel_eq_of_toFiniteLabel_eq _ fef.valid.finite) := by
  rcases fef with ⟨sp, lm1⟩
  dsimp [minLength_def]
  rw [← ENat.coe_inj, ← sp.minLength?_eq_natCast_minLength, ← sp.snd.length?_eq_natCast_length]
  exact lm1.wShape.minLength?_eq_snd_length?


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

theorem initOf_minLength {s: ts.S} : (initOf ts s).minLength = 0 := by
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

end FiniteExecutionFragment

end Nemonuri.TransitionSystem

end
