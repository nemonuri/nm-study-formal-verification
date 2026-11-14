module

public import Nemonuri.TransitionSystem.FiniteExecutionFragment

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

theorem stepOnce_stepN_minLength_le_stepN_minLength_add_one [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ)
  : (ex.stepN (ex.stepOnce fef) fuel).minLength ≤ (ex.stepN fef fuel).minLength + 1 := by
  rcases lm1: fuel with _ | ⟨fuel⟩
  · dsimp [stepN]
    exact ex.stepOnce_minLength_le_minLength_add_one fef
  · dsimp [stepN]
    exact ex.stepOnce_stepN_minLength_le_stepN_minLength_add_one (ex.stepOnce fef) fuel


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
  have lm4 := ex.stepOnce_minLength_le_minLength_add_one fef2
  have lm5 := ex.stepN_minLength_le_add_fuel (ex.stepOnce fef2) i
-/
  --have lm6 := Nat.add_le_add_right



--def run [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) : Stream'.Seq (Step ts)

/-
def runStep? [DecidablePred ts.IsTerminal] (ex: Executor ts) (si: ↑ts.I) (fuel: ℕ) : Option (Step ts) :=
  let fef := ex.runN (.initOf ts si.val) fuel
-/
--OptionProd ts.S ts.Act := ex.runN (.initOf ts si.val) (fuel + 1) |>.getAt? fuel


--open Classical in
--def DeterministicOn (exs: Set (Executor ts)) (seto: Setoid (ts.S → ℕ →)) :


/-
theorem runOnce_unique_iff [DecidablePred ts.IsTerminal] (ex1 ex2: Executor ts) : ex1.runOnce = ex2.runOnce := by
  simp [funext_iff]
  intro fef
  dsimp [runOnce]
  split
  · rfl
  · rename_i lm1
    revert lm1
    simp [isTerminal_iff]
    intro act spo lm1
    refine congrArg fef.step ?_
    dsimp [stepROf]
    simp
-/
    --simp [isTerminal_iff] at lm1

/-
theorem deterministic [DecidablePred ts.IsTerminal] (req: ts.IsActionDeterministic) (ex1 ex2: Executor ts) : ex1.runFromN = ex2.runFromN := by
  simp [funext_iff]
  intro s lm1 fuel
  dsimp [runFromN]
  generalize lm2: FiniteExecutionFragment.initOf ts s = fef
  rcases req with ⟨lm3, lm4⟩
  simp [det_norm] at lm4
  induction fuel with
  | zero => dsimp [runN]
  | succ fuel lm5 =>
    dsimp [runN]
-/



end Executor



open Classical in
variable (ts) in
def IsDeterministicOn (exs: Set (Executor ts)) (srel: Setoid (↑ts.I → Stream'.Seq (Step ts))) : Prop :=
  ∀⦃ex1⦄, (ex1 ∈ exs) → ∀⦃ex2⦄, (ex2 ∈ exs) → srel.r (ex1.runStepStreamSeq) (ex2.runStepStreamSeq)


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
