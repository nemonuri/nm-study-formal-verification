module

public import Nemonuri.Executions.ExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment

open Nemonuri.HasLabel

inductive ExprRaw (ts: TransitionSystem) where
  | finite1 (total: ts.FiniteExecutionFragmentRaw)
  | finite2 (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
  | infinite1 (pre: ts.FiniteExecutionFragmentRaw)

namespace ExprRaw

variable {ts: TransitionSystem}

inductive Label where
  | finite1
  | finite2
  | infinite1
  deriving DecidableEq, Repr, Fintype

def toLabel : ExprRaw ts → Label
  | .finite1 _ => .finite1
  | .finite2 _ _ => .finite2
  | .infinite1 _ => .infinite1

@[defeq, simp]
theorem finite1_toLabel {x} : (@ExprRaw.finite1 ts x).toLabel = .finite1 := rfl

@[defeq, simp]
theorem finite2_toLabel {x1 x2} : (@ExprRaw.finite2 ts x1 x2).toLabel = .finite2 := rfl

@[defeq, simp]
theorem infinite1_toLabel {x} : (@ExprRaw.infinite1 ts x).toLabel = .infinite1 := rfl

instance : HasLabel Label (ExprRaw ts) := ⟨toLabel⟩


def Label.toSeqLabel : Label → Sequence.Label
  | .finite1 | .finite2 => .finite
  | .infinite1 => .infinite

def toSeqLabel (raw: ExprRaw ts) : Sequence.Label := raw.toLabel.toSeqLabel

@[defeq, simp]
theorem finite1_toSeqLabel {x} : (@ExprRaw.finite1 ts x).toSeqLabel = .finite := rfl

@[defeq, simp]
theorem finite2_toSeqLabel {x1 x2} : (@ExprRaw.finite2 ts x1 x2).toSeqLabel = .finite := rfl

@[defeq, simp]
theorem infinite1_toSeqLabel {x} : (@ExprRaw.infinite1 ts x).toSeqLabel = .infinite := rfl

instance : HasLabel Sequence.Label (ExprRaw ts) := ⟨toSeqLabel⟩




def singleState (s: ts.S) : ExprRaw ts := .finite1 (.singleState s)

section SingleState

variable {s: ts.S}

@[defeq, simp]
theorem singleState_toLabel : (singleState s).toLabel = .finite1 := rfl

@[defeq, simp]
theorem singleState_toSeqLabel : (singleState s).toSeqLabel = .finite := rfl

end SingleState


def ellipsis : ExprRaw ts := .infinite1 (⟨[],[]⟩)

section Ellipsis

@[defeq, simp]
theorem ellipsis_toLabel : (@ellipsis ts).toLabel = .infinite1 := rfl

@[defeq, simp]
theorem ellipsis_toSeqLabel : (@ellipsis ts).toSeqLabel = .infinite := rfl

end Ellipsis


def consEllipsis : ExprRaw ts → ExprRaw ts
  | .finite1 total => .finite2 (⟨[],[]⟩) total
  | x => x

theorem consEllipsis_preserves_seqLabel : HasLabel.Preserves Sequence.Label (@consEllipsis ts) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl


def stepL (tail: ExprRaw ts) (s: ts.S) (a: ts.Act) : ExprRaw ts :=
  match tail with
  | .finite1 total => .finite1 (total.stepL s a)
  | .finite2 pre post => .finite2 (pre.stepL s a) post
  | .infinite1 pre => .infinite1 (pre.stepL s a)

theorem stepL_preserves_label {s a} : HasLabel.Preserves Label (@stepL ts · s a) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl

theorem stepL_preserves_seqLabel {s a} : HasLabel.Preserves Sequence.Label (@stepL ts · s a) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl


def stepL' (s: ts.S) (a: ts.Act) (tail: ExprRaw ts) : ExprRaw ts := tail.stepL s a

@[defeq]
theorem stepL_eq_stepL' {tail s a} : (@stepL ts tail s a) = (@stepL' ts s a tail) := rfl

theorem stepL'_preserves_label {s a} : HasLabel.Preserves Label (@stepL' ts s a) := @stepL_preserves_label ts s a

theorem stepL'_preserves_seqLabel {s a} : HasLabel.Preserves Sequence.Label (@stepL' ts s a) := @stepL_preserves_seqLabel ts s a


--def pre :

section

variable {tail: ExprRaw ts} {s: ts.S} {a: ts.Act}

--theorem stepL_finite1 (req: tail.toSeqLabel = .finite) : (tail.stepL s a)

end

instance : Coe ts.S (ExprRaw ts) := ⟨singleState⟩

end ExprRaw



end Nemonuri.TransitionSystem.ExecutionFragment

end
