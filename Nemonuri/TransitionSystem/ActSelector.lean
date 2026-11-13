module

public import Nemonuri.TransitionSystem.FiniteExecutionFragment

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

structure ExecutorStruct (ts: TransitionSystem) where
  select: (FiniteExecutionFragment ts) → ts.Act
  exec: ts.S → ts.Act → ts.S

structure IsExecutor {ts: TransitionSystem} (es: ts.ExecutorStruct) : Prop where
  tr_of_not_termial (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState) : fef.lastState ─⌞(es.select fef)⌟→{ts} (es.exec fef.lastState (es.select fef))

structure Executor (ts: TransitionSystem) extends toStruct: ts.ExecutorStruct where
  valid: IsExecutor toStruct

namespace Executor

variable {ts: TransitionSystem}

def stepROf (ex: Executor ts) (fef: FiniteExecutionFragment ts) (req: ¬ts.IsTerminal fef.lastState) : StepR ts fef.lastState where
  act := ex.select fef
  post := ex.exec fef.lastState (ex.select fef)
  valid := by exact ex.valid.tr_of_not_termial fef req

def runOnce [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) : FiniteExecutionFragment ts :=
  if h1: ts.IsTerminal fef.lastState then fef else fef.step (ex.stepROf fef h1)

def runN [DecidablePred ts.IsTerminal] (ex: Executor ts) (fef: FiniteExecutionFragment ts) (fuel: ℕ) : FiniteExecutionFragment ts :=
  match fuel with
  | 0 => fef
  | fuel + 1 => ex.runN (ex.runOnce fef) fuel


end Executor

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
