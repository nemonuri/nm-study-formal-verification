module

public import Nemonuri.TransitionSystem.FiniteExecutionFragment
public import Nemonuri.Sequence.Potential

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem


def ActEquiv (ts: TransitionSystem) (a1 a2: ts.Act) : Prop := ∀⦃s1 s2: ts.S⦄, ts.tr s1 a1 s2 ↔ ts.tr s1 a2 s2

namespace ActEquiv

theorem equivalence (ts: TransitionSystem) : Equivalence (ts.ActEquiv) := by
  refine .mk ?_ ?_ ?_
  · dsimp [ActEquiv]
    intro _ _ _
    rfl
  · dsimp [ActEquiv]
    intro a1 a2 lm1
    conv => ext; ext; rw [Iff.comm]
    exact lm1
  · dsimp [ActEquiv]
    intro a1 a2 a3 lm1 lm2 s1 s2
    specialize @lm1 s1 s2
    specialize @lm2 s1 s2
    exact lm1.trans lm2

end ActEquiv


structure ExecutorStruct (ts: TransitionSystem) where
  select: (FiniteExecutionFragment ts) → ts.Act
  exec: ts.S → ts.Act → ts.S

structure IsExecutor {ts: TransitionSystem} (es: ts.ExecutorStruct) : Prop where
  tr_of_not_termial (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState) : fef.lastState ─⌞(es.select fef)⌟→{ts} (es.exec fef.lastState (es.select fef))

--@[ext]
structure Executor (ts: TransitionSystem) extends toStruct: ts.ExecutorStruct where
  valid: IsExecutor toStruct

namespace Executor

variable {ts: TransitionSystem}

--def Mem (ex: Executor ts) (fef: FiniteExecutionFragment ts) : Prop := fef.lastState ─⌞(ex.select fef)⌟→{ts} (ex.exec fef.lastState (ex.select fef))

--def Rel (ex: Executor ts) (spr: ts.S) (act: ts.Act) : Prop := spr ─⌞(act)⌟→{ts} ex.exec spr (ex.select )

/-
theorem ext_of_actionDeterministic (req1: ts.IsActionDeterministic) (ex1 ex2: Executor ts) (req2: ex1.exec = ex2.exec) : ex1 = ex2 := by
  rcases ex1 with ⟨⟨se1, ex1⟩, ⟨lm1⟩⟩
  rcases ex2 with ⟨⟨se2, ex2⟩, ⟨lm2⟩⟩
  dsimp at lm1 lm2
  simp [funext_iff] at req2 ⊢
  refine ⟨?_, req2⟩
  intro fef
  simp [isTerminal_iff] at lm1 lm2
  specialize req2 fef.lastState
  specialize lm1 fef (se2 fef) (ex2 fef.lastState (se2 fef))
  specialize lm2 fef (se1 fef) (ex1 fef.lastState (se1 fef))
  have lm3 := Iff.intro lm1 lm2
-/
/-
  simp [isTerminal_iff] at lm1 lm2
  rcases req1 with ⟨lm3, lm4⟩
  simp [det_norm] at lm4
  intro s a
  specialize lm4 s a
-/


def stepROf (ex: Executor ts) (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState) : StepR ts fef.lastState where
  act := ex.select fef
  post := ex.exec fef.lastState (ex.select fef)
  valid := by exact ex.valid.tr_of_not_termial fef req

def stepOnce [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) : FiniteExecutionFragment ts :=
  if h1: ts.IsTerminal fef.lastState then fef else fef.step (ex.stepROf fef h1)

def stepN [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ) : FiniteExecutionFragment ts :=
  match fuel with
  | 0 => fef
  | fuel + 1 => ex.stepN (ex.stepOnce fef) fuel

def runN [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) : ℕ → FiniteExecutionFragment ts := ex.stepN (.initOf ts si.val)

def runStep? [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) (i: ℕ) : Option (Step ts) := (ex.runN si (i + 1)).stepAt? i


theorem minLength_le_stepOnce [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts)
  : fef.minLength ≤ (ex.stepOnce fef).minLength := by
  dsimp [stepOnce]
  split
  · exact Nat.le_refl _
  · simp [FiniteExecutionFragment.step_minLength]

theorem stepOnce_minLength_le_minLength_add_one [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts)
  : (ex.stepOnce fef).minLength ≤ (fef.minLength + 1) := by
  dsimp [stepOnce]
  split
  · simp
  · simp [FiniteExecutionFragment.step_minLength]

theorem stepOnce_of_not_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState)
  : ex.stepOnce fef = fef.step (ex.stepROf fef req) := by
  dsimp [stepOnce]
  simp [req]


open FiniteExecutionFragment in
theorem stepOnce_minLength_eq_minLength_iff_stepOnce_eq_self [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts)
  : ((ex.stepOnce fef).minLength = fef.minLength) ↔ (ex.stepOnce fef = fef) := by
  dsimp [stepOnce]
  split <;> rename_i lm1
  · simp
  · simp [step_minLength, step_ne_self]


theorem stepOnce_minLength_eq_minLength_iff_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts)
  : ((ex.stepOnce fef).minLength = fef.minLength) ↔ ts.IsTerminal fef.lastState := by
  rw [ex.stepOnce_minLength_eq_minLength_iff_stepOnce_eq_self fef]
  dsimp [stepOnce]
  simp [FiniteExecutionFragment.step_ne_self]

theorem stepOnce_minLength_eq_minLength_add_one_iff_not_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts)
  : ((ex.stepOnce fef).minLength = fef.minLength + 1) ↔ (¬ts.IsTerminal fef.lastState) := by
  dsimp [stepOnce]
  split <;> (rename_i lm1; simp [lm1])
  exact fef.step_minLength _

theorem stepOnce_eq_self_iff_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts)
  : (ex.stepOnce fef = fef) ↔ ts.IsTerminal fef.lastState :=
  calc
    _ ↔ _ := ex.stepOnce_minLength_eq_minLength_iff_stepOnce_eq_self fef |>.symm
    _ ↔ _ := ex.stepOnce_minLength_eq_minLength_iff_isTerminal fef


theorem minLength_le_stepN [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ)
  : fef.minLength ≤ (ex.stepN fef fuel).minLength := by
  rcases lm3: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
    exact Nat.le_refl _
  · dsimp [stepN]
    have lm1 := ex.minLength_le_stepN (ex.stepOnce fef) fuel
    have lm2 := ex.minLength_le_stepOnce fef
    exact Trans.trans lm2 lm1
  termination_by fuel
  decreasing_by
    subst lm3
    simp

theorem stepN_minLength_le_add_fuel [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ)
  : (ex.stepN fef fuel).minLength ≤ (fef.minLength + fuel) := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
    exact Nat.le_refl _
  · dsimp [stepN]
    have lm2 := ex.stepN_minLength_le_add_fuel (ex.stepOnce fef) fuel
    have lm3 := ex.stepOnce_minLength_le_minLength_add_one fef
    replace lm3 := Nat.add_le_add_right lm3 fuel
    calc
      _ ≤ _ := lm2
      _ ≤ _ := lm3
      _ = fef.minLength + (fuel + 1) := by
        rw [Nat.add_assoc]
        conv => lhs; arg 2; rw [Nat.add_comm]

theorem stepN_minLength_le_and_le [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ)
  : (fef.minLength ≤ (ex.stepN fef fuel).minLength) ∧ ((ex.stepN fef fuel).minLength ≤ (fef.minLength + fuel)) :=
  ⟨ex.minLength_le_stepN fef fuel, ex.stepN_minLength_le_add_fuel fef fuel⟩

theorem stepOnce_stepN_minLength_le_stepN_minLength_add_one [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ)
  : (ex.stepN (ex.stepOnce fef) fuel).minLength ≤ (ex.stepN fef fuel).minLength + 1 := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
    exact ex.stepOnce_minLength_le_minLength_add_one fef
  · dsimp [stepN]
    exact ex.stepOnce_stepN_minLength_le_stepN_minLength_add_one (ex.stepOnce fef) fuel

@[defeq]
theorem stepN_add_one_def [DecidablePred ts.IsTerminal] {ex: Executor ts} {fef} {fuel: ℕ} : ex.stepN fef (fuel + 1) = ex.stepN (ex.stepOnce fef) fuel := rfl

/-
theorem stepN_minLength_le_of_minLength_le [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef1 fef2: FiniteExecutionFragment ts) (req: fef1.minLength ≤ fef2.minLength) (fuel: ℕ)
  : (ex.stepN fef1 fuel).minLength ≤ (ex.stepN fef2 fuel).minLength := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
    exact req
  · dsimp [stepN]
    have lm2 req := ex.stepN_minLength_le_of_minLength_le (ex.stepOnce fef1) (ex.stepOnce fef2) req fuel
    refine lm2 ?_
    dsimp [stepOnce]
-/
    --have lm3 := ex.stepOnce_minLength_le_minLength_add_one fef1
    --have lm4 := ex.minLength_le_stepOnce fef2

@[defeq]
theorem stepN_zero_minLength_eq_minLength [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) : (ex.stepN fef 0).minLength = fef.minLength := by
  dsimp [stepN]


theorem stepN_minLength_eq_minLength_of_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (req: ts.IsTerminal fef.lastState) (fuel: ℕ)
  : ((ex.stepN fef fuel).minLength = fef.minLength) := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
  · dsimp [stepN]
    rw [ex.stepOnce_eq_self_iff_isTerminal fef |>.mpr req]
    exact ex.stepN_minLength_eq_minLength_of_isTerminal fef req fuel

theorem stepN_one_minLength_eq_minLength_add_one_of_not_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState)
  : (ex.stepN fef 1).minLength = fef.minLength + 1 := by
  have lm1 := ex.stepOnce_minLength_eq_minLength_add_one_iff_not_isTerminal fef |>.mpr req
  dsimp [stepN]
  exact lm1

theorem minLength_lt_stepN_pos_minLength_of_not_isTerminal [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ) (req1: 0 < fuel) (req2: ¬ts.IsTerminal fef.lastState)
  : fef.minLength < (ex.stepN fef fuel).minLength := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · simp [lm1] at req1
  · dsimp [stepN]
    generalize lm2: ex.stepOnce fef = fef2
    have lm3 := ex.minLength_le_stepN fef2 fuel
    have lm4 := ex.stepOnce_minLength_eq_minLength_add_one_iff_not_isTerminal fef |>.mpr req2
    rewrite [Eq.comm] at lm2
    subst lm2
    rewrite [lm4] at lm3
    simp at lm3
    exact lm3


theorem stepN_minLength_le_stepN_add_one_minLength [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ)
  : (ex.stepN fef fuel).minLength ≤ (ex.stepN fef (fuel + 1)).minLength := by
  by_cases lm1: ts.IsTerminal fef.lastState
  · have lm2 := ex.stepN_minLength_eq_minLength_of_isTerminal _ lm1
    simp [lm2]
  · rcases lm2: fuel with _ | ⟨fuel⟩
    · dsimp [stepN_zero_minLength_eq_minLength]
      rw [ex.stepN_one_minLength_eq_minLength_add_one_of_not_isTerminal _ lm1]
      simp
    · conv =>
        conv => lhs; dsimp [stepN]
        conv =>
          rhs
          rw [← lm2]
          dsimp [stepN]
          rw [lm2]
      exact ex.stepN_minLength_le_stepN_add_one_minLength (ex.stepOnce fef) fuel


theorem stepN_add_minLength_le_stepN_minLength [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel fuel2: ℕ)
  : (ex.stepN fef fuel).minLength ≤ (ex.stepN fef (fuel + fuel2)).minLength := by
  rcases lm1: fuel2 with _ | ⟨fuel2⟩
  · dsimp
    exact Nat.le_refl _
  · have lm3 := ex.stepN_minLength_le_stepN_add_one_minLength fef fuel
    have lm4 := ex.stepN_add_minLength_le_stepN_minLength fef (fuel + 1) fuel2
    conv at lm4 =>
      rhs
      arg 1
      arg 3
      rw [Nat.add_assoc]
      arg 2
      rw [Nat.add_comm]
    exact Nat.le_trans lm3 lm4

open FiniteExecutionFragment in
theorem stepN_fst_getAt_stepN_add_one_getAt [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (i: ℕ) (fuel: ℕ) (req: i ≤ (ex.stepN fef fuel).minLength)
  : (ex.stepN fef fuel).fst.getAt i (natCast_lt_fst_length?_of_le_minLength _ i req) = (ex.stepN fef (fuel + 1)).fst.getAt i (natCast_lt_fst_length?_of_le_minLength _ i (Nat.le_trans req (ex.stepN_minLength_le_stepN_add_one_minLength _ _))) := by
  dsimp [stepN, stepOnce]
  split <;> rename_i lm1
  · rfl
  · let (eq := lm_fp) fuelProxy := fuel
    rcases fuelProxy with _ | ⟨fuelProxy⟩ <;> (rewrite [Eq.comm] at lm_fp; subst lm_fp)
    · dsimp [stepN, step, SequenceProd.stepR]
      rw [← Option.some_inj]
      simp only [← Sequence.getAt?_eq_some_getAt]
      dsimp [Sequence.snoc]
      simp
      intro lm2
      dsimp [stepN_zero_minLength_eq_minLength] at req
      rewrite [fef.fst.length?_eq_natCast_length fef.valid.fst_finite, ENat.coe_inj] at lm2
      rewrite [← lm2, ← fef.minLength_add_one_eq_fst_length] at req
      simp at req
    · dsimp [stepN]
      have lm2 := ex.stepN_fst_getAt_stepN_add_one_getAt (ex.stepOnce fef) i fuelProxy
      simp only [← stepOnce_of_not_isTerminal]
      refine lm2 ?_
      dsimp [← stepN_add_one_def]
      exact req


/-
open FiniteExecutionFragment in
theorem stepN_fst_getAt_eq_fst_getAt [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (i: ℕ) (req: i ≤ fef.minLength) (fuel: ℕ)
  : (ex.stepN fef fuel).fst.getAt i (natCast_lt_fst_length?_of_le_minLength _ i (Nat.le_trans req (ex.minLength_le_stepN fef fuel))) = fef.fst.getAt i (natCast_lt_fst_length?_of_le_minLength fef i req) := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
  · dsimp [stepN]
    have lm2 := ex.stepN_fst_getAt_eq_fst_getAt (ex.stepOnce fef) i (Nat.le_trans req (ex.minLength_le_stepOnce fef)) fuel
    refine Eq.trans lm2 ?_
    dsimp [stepOnce]
    split
    · rfl
    · dsimp [step, SequenceProd.stepR]
      exact fef.fst.snoc_getAt_eq_getAt i _ _
-/



theorem runStep?_isStreamSeq [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) : Stream'.IsSeq (ex.runStep? si) := by
  intro i
  dsimp [runStep?]
  simp [FiniteExecutionFragment.stepAt?_eq_none_iff]
  dsimp [runN]
  generalize lm1: (FiniteExecutionFragment.initOf ts ↑si) = fef
  dsimp [stepN]
  generalize lm2: (ex.stepOnce fef) = fef2
  intro lm3
  have lm4 := ex.stepOnce_stepN_minLength_le_stepN_minLength_add_one fef2 i
  replace lm3 := Nat.add_le_add_right lm3 1
  exact Trans.trans lm4 lm3


def runStepStreamSeq [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) : Stream'.Seq (Step ts) :=
  ⟨ex.runStep? si, ex.runStep?_isStreamSeq si⟩

/-
theorem runStep?_eq_zero [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) x : ex.runStep? si 0 = x := by
  dsimp [runStep?, runN, stepN]
-/

--theorem stepN_getAt?_eq_


end Executor


/-
open Classical in
variable (ts) in
def IsDeterministicOn (exs: Set (Executor ts)) (srel: Setoid (↑ts.I → Stream'.Seq (Step ts))) : Prop :=
  ∀⦃ex1⦄, (ex1 ∈ exs) → ∀⦃ex2⦄, (ex2 ∈ exs) → srel.r (ex1.runStepStreamSeq) (ex2.runStepStreamSeq)
-/

/-
structure ExecutorStruct (ts: TransitionSystem) where
  exec: ts.S → ts.Act → ts.S

structure IsExecutor {ts: TransitionSystem} (es: ts.ExecutorStruct) : Prop where
  post_of_not_termial (spr: ts.S) (act: ts.Act) (req1: ¬ts.IsTerminal spr) (req2: ∃spr, spr ∈ 𝑃𝑜𝑠𝑡{ts}⸨spr, act⸩) : spr ─⌞act⌟→{ts} (es.exec spr act)

structure ActSelectorStruct (ts: TransitionSystem) where
  select (fef: FiniteExecutionFragment ts) : ts.Act

structure IsActSelector {ts: TransitionSystem} (as: ActSelectorStruct ts) : Prop where
  act_of_not_termial (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState) : ∃spr, spr ∈ 𝑃𝑜𝑠𝑡{ts}⸨(fef.lastState), (as.select fef)⸩
-/

end Nemonuri.TransitionSystem

end
