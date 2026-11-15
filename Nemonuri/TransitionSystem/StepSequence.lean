module

public import Nemonuri.TransitionSystem.Executor
public import Nemonuri.Sequence.Potential

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem




structure StepSequenceStruct (ts: TransitionSystem) where
  getAt? : ℕ → Option (Step ts)

structure IsStepSequence {ts: TransitionSystem} (s: StepSequenceStruct ts) : Prop where
  getAt?_isSeq : Stream'.IsSeq s.getAt?
  pre_eq_post (n: ℕ) (step: Step ts) (req: s.getAt? (n + 1) = .some step) : step.pre = ((s.getAt? n).get (getAt?_isSeq.isSome_of_add_one_isSome n (Option.isSome_of_eq_some req))).post

structure StepSequence (ts: TransitionSystem) extends toStruct: StepSequenceStruct ts where
  valid: IsStepSequence toStruct


namespace StepSequence

variable {ts: TransitionSystem}

def toPotentialSequence (s: StepSequence ts) : Sequence.Potential (Step ts) := ⟨s.getAt?, @s.valid.getAt?_isSeq⟩

variable (ts) in
structure FactoryStruct where
  get: ↑ts.I → ℕ → Option (Step ts)

structure IsFactory (s: FactoryStruct ts) : Prop where
  get_zero_eq_self (si: ↑ts.I) : ∀s0 ∈ s.get si 0, s0.pre = si.val
  get_isStepSequence (si: ↑ts.I) : IsStepSequence ⟨s.get si⟩

variable (ts) in
structure Factory extends toStruct: FactoryStruct ts where
  valid: IsFactory toStruct


namespace Factory

def initToSeq (fac: Factory ts) (si: ↑ts.I) : StepSequence ts := ⟨⟨fac.get si⟩, fac.valid.get_isStepSequence si⟩

end Factory

end StepSequence


namespace Executor

variable {ts: TransitionSystem} [DecidablePred ts.IsTerminal]

open FiniteExecutionFragment in
theorem runStep?_isStepSequence (ex: Executor ts) (si: ↑ts.I) : IsStepSequence ⟨ex.runStep? si⟩ := by
  have lm1 : Stream'.IsSeq (ex.runStep? si) := ex.runStep?_isStreamSeq si
  refine .mk lm1 ?_
  dsimp
  intro i step lm2
  have lm3 := lm1.isSome_of_add_one_isSome i (Option.isSome_of_eq_some lm2)
  rewrite [Option.isSome_iff_exists] at lm3
  rcases lm3 with ⟨step2, lm3⟩
  dsimp [Stream'.get] at lm3
  simp [lm3]
  dsimp [runStep?] at lm2 lm3
  simp [stepAt?] at lm2 lm3
  rcases lm2 with ⟨lm2, lm4⟩
  rcases lm3 with ⟨lm3, lm5⟩
  rewrite [Eq.comm] at lm4 lm5
  subst lm4 lm5
  dsimp
  let (eq := lm4) i2 := i + 1
  simp only [← lm4]
  dsimp [runN]
  symm
  refine ex.stepN_fst_getAt_stepN_add_one_getAt (initOf ts ↑si) i2 i2 ?_
  rewrite [← lm4] at lm3
  dsimp [runN] at lm3
  subst i2
  simp
  exact lm3
--  rw [← Option.some_inj]
--  simp only [← Sequence.getAt?_eq_some_getAt]
  --generalize lm6: i + 1 = i2
  --dsimp [runN]
  --have lm7 := ex.stepN_fst_getAt_stepN_add_one_getAt (initOf ts ↑si) i2 i2

/-
  generalize lm6: ex.runN si (i + 1 + 1) = fef1
  generalize lm7: ex.runN si (i + 1) = fef2
  rewrite [lm6] at lm2
  rewrite [lm7] at lm3
  generalize lm8: i + 1 = i2 at lm7 lm6
  dsimp [runN] at lm6 lm7
  generalize lm9: initOf ts ↑si = fef0 at lm6 lm7
  dsimp [stepN] at lm6
  have lm10 := ex.stepOnce_stepN_minLength_le_stepN_minLength_add_one fef0 i2
  rewrite [lm6, lm7] at lm10
  have lm11 := ex.stepN_minLength_le_add_fuel fef0 i2
  rewrite [lm7] at lm11
  have lm12 := congrArg (minLength) lm9
  rewrite [initOf_minLength] at lm12
  rewrite [← lm12, ← lm8] at lm11
  simp at lm11
  have lm13 : fef2.minLength = i + 1 := by omega
  clear lm11
  rewrite [lm13] at lm10
  have lm14 : fef1.minLength = i + 2 := by omega
  simp [lm14, lm13]
  dsimp [← stepN_add_one_def] at lm6
  simp [← lm6, ← lm7]
  have lm15 := ex.stepN_fst_getAt_stepN_add_one_getAt fef0 (i + 1) i2
  symm
  refine lm15 ?_
  rw [lm7, lm13]
-/

open FiniteExecutionFragment in
def factory (ex: Executor ts) : StepSequence.Factory ts where
  get := ex.runStep?
  valid := by
    refine .mk ?_ ?_
    · intro si step lm1
      simp at lm1
      dsimp [runStep?] at lm1
      simp [FiniteExecutionFragment.stepAt?] at lm1
      rcases lm1 with ⟨lm1, lm2⟩
      rw [← lm2]
      simp
      generalize lm3: ex.runN si 1 = fef at lm1
      dsimp [runN, stepN] at lm3
      generalize lm4: initOf ts ↑si = fef2 at lm3
      by_cases lm5: ts.IsTerminal fef2.lastState
      · have lm6 := ex.stepOnce_minLength_eq_minLength_iff_isTerminal fef2 |>.mpr lm5
        rewrite [← lm3, lm6, ← lm4, initOf_minLength] at lm1
        simp at lm1
      · have lm6 := ex.stepOnce_of_not_isTerminal _ lm5
        rewrite [Eq.comm] at lm4 lm3
        subst lm4 lm3
        simp [lm6]
        rw [← Option.some_inj, ← Sequence.getAt?_eq_some_getAt]
        dsimp [FiniteExecutionFragment.step, SequenceProd.stepR, Sequence.snoc]
        have lm3 := initOf_minLength si.val |> congrArg (· + 1)
        rw [minLength_add_one_eq_fst_length, ← ENat.coe_inj, ← Sequence.length?_eq_natCast_length] at lm3
        simp [lm3]
        dsimp [initOf, SequenceProd.singleFst, Sequence.single]
    · exact ex.runStep?_isStepSequence

end Executor


open Classical in
def IsDeterministicOn (ts: TransitionSystem) (exs: Set (Executor ts)) (srel: Setoid (StepSequence.Factory ts)) : Prop :=
  ∀⦃ex1⦄, (ex1 ∈ exs) → ∀⦃ex2⦄, (ex2 ∈ exs) → srel.r ex1.factory ex2.factory


namespace IsDeterministicOn







end IsDeterministicOn

end Nemonuri.TransitionSystem

end
