module

public import Nemonuri.Executions.ExecutionFragment.Syntax.Raws

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

variable {ts: TransitionSystem}


def whole (x: SyntaxRaw ts) (req: x.toLabel = .unique) : ts.FiniteExecutionFragmentRaw :=
  match x with
  | .unique whole => whole
  | .finites _ _ | .infinites _ => absurd req (by simp)

section Whole

@[defeq, simp]
theorem unique_whole {x} : (@SyntaxRaw.unique ts x).whole unique_toLabel = x := rfl

@[defeq, simp]
theorem singleState_whole_states {x} : ((@SyntaxRaw.singleState ts x).whole singleState_toLabel).states = [x] := rfl

@[defeq, simp]
theorem singleState_whole_actions {x} : ((@SyntaxRaw.singleState ts x).whole singleState_toLabel).actions = [] := rfl

section StepL

variable {tail: SyntaxRaw ts} {s: ts.S} {a: ts.Act}

theorem stepL_whole_eq_whole_stepL_aux (req: tail.toLabel = .unique) : (tail.stepL s a).toLabel = .unique := by
  cases tail <;> try simp at req
  · dsimp [stepL]

theorem stepL_whole_eq_whole_stepL (req: tail.toLabel = .unique)
  : (SyntaxRaw.stepL tail s a).whole (stepL_whole_eq_whole_stepL_aux req) = (tail.whole req).stepL s a := by
  cases tail <;> try simp at req
  · rfl

/-
@[simp]
theorem stepL_whole_states_eq_whole_stepL_states (req: tail.toLabel = .unique)
  : ((SyntaxRaw.stepL tail s a).whole (stepL_whole_eq_whole_stepL_aux req)).states = ((tail.whole req).stepL s a).states :=
  congrArg FiniteExecutionFragmentRaw.states (stepL_whole_eq_whole_stepL req)

@[simp]
theorem stepL_whole_actions_eq_whole_stepL_actions (req: tail.toLabel = .unique)
  : ((SyntaxRaw.stepL tail s a).whole (stepL_whole_eq_whole_stepL_aux req)).actions = ((tail.whole req).stepL s a).actions :=
  congrArg FiniteExecutionFragmentRaw.actions (stepL_whole_eq_whole_stepL req)
-/

end StepL

end Whole



def preOrWhole : SyntaxRaw ts → ts.FiniteExecutionFragmentRaw
  | .unique whole => whole
  | .finites pre _ => pre
  | .infinites pre => pre

section PreOrWhole

@[defeq, simp]
theorem unique_preOrWhole {x} : (@SyntaxRaw.unique ts x).preOrWhole = x := rfl

@[defeq, simp]
theorem finites_preOrWhole {x1 x2} : (@SyntaxRaw.finites ts x1 x2).preOrWhole = x1 := rfl

@[defeq, simp]
theorem infinites_preOrWhole {x} : (@SyntaxRaw.infinites ts x).preOrWhole = x := rfl

@[defeq, simp]
theorem singleState_preOrWhole_states {s} : (@singleState ts s).preOrWhole.states = [s] := rfl

@[defeq, simp]
theorem singleState_preOrWhole_actions {s} : (@singleState ts s).preOrWhole.actions = [] := rfl

@[defeq, simp]
theorem ellipsis_preOrWhole_states : (@ellipsis ts).preOrWhole.states = [] := rfl

@[defeq, simp]
theorem ellipsis_preOrWhole_actions : (@ellipsis ts).preOrWhole.actions = [] := rfl

@[simp]
theorem consEllipsis_preOrWhole_states {x} (req: x.toLabel = .unique) : (@consEllipsis ts x).preOrWhole.states = [] := by
  cases x <;> simp at req
  · rfl

@[simp]
theorem consEllipsis_preOrWhole_actions {x} (req: x.toLabel = .unique) : (@consEllipsis ts x).preOrWhole.actions = [] := by
  cases x <;> simp at req
  · rfl

section StepL

variable {tail: SyntaxRaw ts} {s: ts.S} {a: ts.Act}

theorem stepL_preOrWhole_eq_preOrWhole_stepL : (stepL tail s a).preOrWhole = (tail.preOrWhole.stepL s a) := by
  cases tail <;> rfl

@[simp]
theorem stepL_preOrWhole_states_eq_preOrWhole_stepL_states : (stepL tail s a).preOrWhole.states = (tail.preOrWhole.stepL s a).states :=
  congrArg FiniteExecutionFragmentRaw.states stepL_preOrWhole_eq_preOrWhole_stepL

@[simp]
theorem stepL_preOrWhole_actions_eq_preOrWhole_stepL_actions : (stepL tail s a).preOrWhole.actions = (tail.preOrWhole.stepL s a).actions :=
  congrArg FiniteExecutionFragmentRaw.actions stepL_preOrWhole_eq_preOrWhole_stepL

end StepL

end PreOrWhole





end Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

end
