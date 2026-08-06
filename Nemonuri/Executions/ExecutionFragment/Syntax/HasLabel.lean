module

public import Nemonuri.HasLabel
public import Nemonuri.Executions.ExecutionFragment.Syntax.Projections

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

open HasLabel

variable {ts: TransitionSystem}

theorem toLabel_eq_toLabelAt : (@SyntaxRaw.toLabel ts) = (toLabelAt Label (SyntaxRaw ts)) := rfl

theorem toSeqLabel_eq_toLabelAt : (@SyntaxRaw.toSeqLabel ts) = (toLabelAt Sequence.Label (SyntaxRaw ts)) := rfl


theorem consEllipsis_preserves_seqLabel : HasLabel.Preserves Sequence.Label (@consEllipsis ts) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl

protected theorem stepL_preserves_label {s a} : HasLabel.Preserves Label (@stepL ts · s a) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl

protected theorem stepL_preserves_seqLabel {s a} : HasLabel.Preserves Sequence.Label (@stepL ts · s a) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl



def stepLFlip (s: ts.S) (a: ts.Act) (tail: SyntaxRaw ts) : SyntaxRaw ts := tail.stepL s a

section StepLFlip

variable {tail: SyntaxRaw ts} {s: ts.S} {a: ts.Act}

@[defeq]
theorem stepL_eq_stepLFlip : (stepL tail s a) = (stepLFlip s a tail) := rfl

theorem stepLFlip_preserves_label : HasLabel.Preserves Label (stepLFlip s a) := @SyntaxRaw.stepL_preserves_label ts s a

theorem stepLFlip_preserves_seqLabel : HasLabel.Preserves Sequence.Label (stepLFlip s a) := @SyntaxRaw.stepL_preserves_seqLabel ts s a



theorem stepLFlip_whole_eq_whole_stepLFlip (req: toLabelAt Label (SyntaxRaw ts) tail = .unique)
  : ((stepLFlip s a tail).whole (stepLFlip_preserves_label.cancel.trans req)) = (tail.whole req).stepL s a := by
  dsimp [← stepL_eq_stepLFlip]
  exact stepL_whole_eq_whole_stepL req

@[simp]
theorem stepLFlip_whole_states_eq_whole_stepLFlip_states (req: toLabelAt Label (SyntaxRaw ts) tail = .unique)
  : ((stepLFlip s a tail).whole (stepLFlip_preserves_label.cancel.trans req)).states = ((tail.whole req).stepL s a).states :=
  congrArg _ (stepLFlip_whole_eq_whole_stepLFlip req)

@[simp]
theorem stepLFlip_whole_actions_eq_whole_stepLFlip_actions (req: toLabelAt Label (SyntaxRaw ts) tail = .unique)
  : ((stepLFlip s a tail).whole (stepLFlip_preserves_label.cancel.trans req)).actions = ((tail.whole req).stepL s a).actions :=
  congrArg _ (stepLFlip_whole_eq_whole_stepLFlip req)

end StepLFlip


@[defeq, simp]
theorem unique_toLabelAt {x} : toLabelAt Label (SyntaxRaw ts) (.unique x) = .unique := rfl

@[defeq, simp]
theorem finites_toLabelAt {x1 x2} : toLabelAt Label (SyntaxRaw ts) (.finites x1 x2) = .finites := rfl

@[defeq, simp]
theorem infinites_toLabelAt {x} : toLabelAt Label (SyntaxRaw ts) (.infinites x) = .infinites := rfl


@[defeq, simp]
theorem unique_toLabelAt_seq {x} : toLabelAt Sequence.Label (SyntaxRaw ts) (.unique x) = .finite := rfl

@[defeq, simp]
theorem finites_toLabelAt_seq {x1 x2} : toLabelAt Sequence.Label (SyntaxRaw ts) (.finites x1 x2) = .finite := rfl

@[defeq, simp]
theorem infinites_toLabelAt_seq {x} : toLabelAt Sequence.Label (SyntaxRaw ts) (.infinites x) = .infinite := rfl


@[defeq, simp]
theorem singleState_toLabelAt {s} : toLabelAt Label (SyntaxRaw ts) (singleState s) = .unique := rfl

@[defeq, simp]
theorem singleState_toLabelAt_seq {s} : toLabelAt Sequence.Label (SyntaxRaw ts) (singleState s) = .finite := rfl


@[defeq, simp]
theorem ellipsis_toLabelAt : toLabelAt Label _ (@ellipsis ts) = .infinites := rfl

@[defeq, simp]
theorem ellipsis_toLabelAt_seq : toLabelAt Sequence.Label _ (@ellipsis ts) = .infinite := rfl


end Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

end
