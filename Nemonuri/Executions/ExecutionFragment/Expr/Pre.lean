module

public import Nemonuri.Executions.ExecutionFragment.Expr.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

variable {ts: TransitionSystem}


def pre : ExprRaw ts → ts.FiniteExecutionFragmentRaw
  | .finite1 total => total
  | .finite2 pre _ => pre
  | .infinite1 pre => pre



@[defeq, simp]
theorem finite1_pre {x} : (@ExprRaw.finite1 ts x).pre = x := rfl

@[defeq, simp]
theorem finite2_pre {x1 x2} : (@ExprRaw.finite2 ts x1 x2).pre = x1 := rfl

@[defeq, simp]
theorem infinite1_pre {x} : (@ExprRaw.infinite1 ts x).pre = x := rfl

@[defeq, simp]
theorem singleState_pre_states {s} : (@singleState ts s).pre.states = [s] := rfl

@[defeq, simp]
theorem singleState_pre_actions {s} : (@singleState ts s).pre.actions = [] := rfl

@[defeq, simp]
theorem ellipsis_pre_states : (@ellipsis ts).pre.states = [] := rfl

@[defeq, simp]
theorem ellipsis_pre_actions : (@ellipsis ts).pre.actions = [] := rfl

@[simp]
theorem consEllipsis_pre_states {x} (req: x.toLabel = .finite1) : (@consEllipsis ts x).pre.states = [] := by
  cases x <;> simp at req
  · rfl

@[simp]
theorem consEllipsis_pre_actions {x} (req: x.toLabel = .finite1) : (@consEllipsis ts x).pre.actions = [] := by
  cases x <;> simp at req
  · rfl

section StepL

variable {tail: ExprRaw ts} {s: ts.S} {a: ts.Act}

theorem stepL_pre_eq_pre_stepL : (stepL tail s a).pre = (tail.pre.stepL s a) := by
  cases tail <;> rfl

@[simp]
theorem stepL_pre_states_eq_pre_stepL_states : (stepL tail s a).pre.states = (tail.pre.stepL s a).states :=
  congrArg FiniteExecutionFragmentRaw.states stepL_pre_eq_pre_stepL

@[simp]
theorem stepL_pre_actions_eq_pre_stepL_actions : (stepL tail s a).pre.actions = (tail.pre.stepL s a).actions :=
  congrArg FiniteExecutionFragmentRaw.actions stepL_pre_eq_pre_stepL

end StepL

--theorem stepL_pre_states






end Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

end
