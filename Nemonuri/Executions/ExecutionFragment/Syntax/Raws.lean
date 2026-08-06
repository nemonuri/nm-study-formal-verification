module

public import Nemonuri.Executions.ExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment

open Nemonuri.HasLabel

inductive SyntaxRaw (ts: TransitionSystem) where
  | unique (whole: ts.FiniteExecutionFragmentRaw)
  | finites (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
  | infinites (pre: ts.FiniteExecutionFragmentRaw)

namespace SyntaxRaw

variable {ts: TransitionSystem}

inductive Label where
  | unique
  | finites
  | infinites
  deriving DecidableEq, Repr, Fintype

def toLabel : SyntaxRaw ts → Label
  | unique _ => .unique
  | finites _ _ => .finites
  | infinites _ => .infinites

@[defeq, simp]
theorem unique_toLabel {x} : (@SyntaxRaw.unique ts x).toLabel = .unique := rfl

@[defeq, simp]
theorem finites_toLabel {x1 x2} : (@SyntaxRaw.finites ts x1 x2).toLabel = .finites := rfl

@[defeq, simp]
theorem infinites_toLabel {x} : (@SyntaxRaw.infinites ts x).toLabel = .infinites := rfl

instance : HasLabel Label (SyntaxRaw ts) := ⟨toLabel⟩


def Label.toSeqLabel : Label → Sequence.Label
  | .unique | .finites => .finite
  | .infinites => .infinite

def toSeqLabel (raw: SyntaxRaw ts) : Sequence.Label := raw.toLabel.toSeqLabel

@[defeq, simp]
theorem unique_toSeqLabel {x} : (@unique ts x).toSeqLabel = .finite := rfl

@[defeq, simp]
theorem finites_toSeqLabel {x1 x2} : (@finites ts x1 x2).toSeqLabel = .finite := rfl

@[defeq, simp]
theorem infinites_toSeqLabel {x} : (@infinites ts x).toSeqLabel = .infinite := rfl

instance : HasLabel Sequence.Label (SyntaxRaw ts) := ⟨toSeqLabel⟩




def singleState (s: ts.S) : SyntaxRaw ts := unique (.singleState s)

section SingleState

variable {s: ts.S}

@[defeq, simp]
theorem singleState_toLabel : (singleState s).toLabel = .unique := rfl

@[defeq, simp]
theorem singleState_toSeqLabel : (singleState s).toSeqLabel = .finite := rfl

end SingleState


def ellipsis : SyntaxRaw ts := infinites (⟨[],[]⟩)

section Ellipsis

@[defeq, simp]
theorem ellipsis_toLabel : (@ellipsis ts).toLabel = .infinites := rfl

@[defeq, simp]
theorem ellipsis_toSeqLabel : (@ellipsis ts).toSeqLabel = .infinite := rfl

end Ellipsis


def consEllipsis : SyntaxRaw ts → SyntaxRaw ts
  | unique total => finites (⟨[],[]⟩) total
  | x => x

/-
theorem consEllipsis_preserves_seqLabel : HasLabel.Preserves Sequence.Label (@consEllipsis ts) := by
  apply Preserves.mk _ ?_
  intro x
  cases x <;> rfl
-/

def stepL (tail: SyntaxRaw ts) (s: ts.S) (a: ts.Act) : SyntaxRaw ts :=
  match tail with
  | unique total => unique (total.stepL s a)
  | finites pre post => finites (pre.stepL s a) post
  | infinites pre => infinites (pre.stepL s a)

/-

-/


def post (ex: SyntaxRaw ts) (req: ex.toSeqLabel = .finite) : ts.FiniteExecutionFragmentRaw :=
  match ex with
  | unique total => total
  | finites _ post => post
  | infinites .. => absurd req (by simp)

section Post

@[defeq, simp]
theorem unique_post {x} : (@unique ts x).post unique_toSeqLabel = x := rfl

@[defeq, simp]
theorem finites_post {x1 x2} : (@finites ts x1 x2).post finites_toSeqLabel = x2 := rfl

end Post



section

variable {tail: SyntaxRaw ts} {s: ts.S} {a: ts.Act}

--theorem stepL_finite1 (req: tail.toSeqLabel = .finite) : (tail.stepL s a)

end

instance : Coe ts.S (SyntaxRaw ts) := ⟨singleState⟩

end SyntaxRaw



end Nemonuri.TransitionSystem.ExecutionFragment

end
