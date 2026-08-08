module

public import Nemonuri.Sequence
public import Nemonuri.TransitionSystem

@[expose] public section

namespace Nemonuri.TransitionSystem


inductive ExecutionSequenceKind where
  | states
  | actions
  deriving DecidableEq, Repr

inductive ExecutionEmptyLabel : ExecutionSequenceKind → Type where
  | states (l: EmptyLabel) : ExecutionEmptyLabel .states
  | actions (l: EmptyLabel) : ExecutionEmptyLabel .actions
  deriving DecidableEq, Repr

namespace ExecutionEmptyLabel


def statesEnumList : List (ExecutionEmptyLabel .states) := [.states .empty, .states .nonempty]

theorem statesEnumList_nodup : statesEnumList.Nodup := by
  dsimp [statesEnumList]
  simp

instance : Fintype (ExecutionEmptyLabel .states) where
  elems := Finset.mk (.ofList statesEnumList) statesEnumList_nodup
  complete x := by
    simp [statesEnumList]
    rcases x with ⟨l⟩ | _
    cases l <;> simp


def actionsEnumList : List (ExecutionEmptyLabel .actions) := [.actions .empty, .actions .nonempty]

theorem actionsEnumList_nodup : actionsEnumList.Nodup := by
  dsimp [actionsEnumList]
  simp

instance : Fintype (ExecutionEmptyLabel .actions) where
  elems := Finset.mk (.ofList actionsEnumList) actionsEnumList_nodup
  complete x := by
    simp [actionsEnumList]
    rcases x with _ | ⟨l⟩
    cases l <;> simp


def toEmptyLabel {seqKind} (x: ExecutionEmptyLabel seqKind) : EmptyLabel :=
  match x with
  | .states l => l
  | .actions l => l

@[defeq, simp]
theorem states_toEmptyLabel {l} : (ExecutionEmptyLabel.states l).toEmptyLabel = l := rfl

@[defeq, simp]
theorem actions_toEmptyLabel {l} : (ExecutionEmptyLabel.actions l).toEmptyLabel = l := rfl

theorem toEmptyLabel_injective {seqKind: ExecutionSequenceKind} : Function.Injective (@toEmptyLabel seqKind) := by
  intro l1 l2 lm1
  cases seqKind <;> cases l1 <;> cases l2 <;> (simp at lm1; rw [lm1])


end ExecutionEmptyLabel

end Nemonuri.TransitionSystem

end
