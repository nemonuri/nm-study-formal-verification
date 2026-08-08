module

public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence
public import Nemonuri.Executions.ExecutionEmptyLabel

@[expose] public section

namespace Nemonuri.TransitionSystem

open Cslib

@[ext]
structure InfiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states : ωSequence ts.S
  actions : ωSequence ts.Act

namespace InfiniteExecutionFragmentRaw

variable {ts: TransitionSystem} {ef: ts.InfiniteExecutionFragmentRaw}

def ofListRepeat (states: List ts.S) (actions: List ts.Act) (req1: states ≠ []) (req2: actions ≠ []) : ts.InfiniteExecutionFragmentRaw :=
  ⟨.ofListRepeat states req1, .ofListRepeat actions req2⟩


def toSeqLabel (_: ts.InfiniteExecutionFragmentRaw) : Sequence.Label := .infinite

def toStatesEmptyLabel (_: ts.InfiniteExecutionFragmentRaw) : ExecutionEmptyLabel .states := .states (.nonempty)

def toActionsEmptyLabel (_: ts.InfiniteExecutionFragmentRaw) : ExecutionEmptyLabel .actions := .actions (.nonempty)

instance : HasLabel Sequence.Label ts.InfiniteExecutionFragmentRaw := ⟨toSeqLabel⟩

instance : HasLabel (ExecutionEmptyLabel .states) ts.InfiniteExecutionFragmentRaw := ⟨toStatesEmptyLabel⟩

instance : HasLabel (ExecutionEmptyLabel .actions) ts.InfiniteExecutionFragmentRaw := ⟨toActionsEmptyLabel⟩



@[defeq, simp]
theorem toSeqLabel_eq_infinite : ef.toSeqLabel = .infinite := rfl

@[defeq, simp]
theorem toStatesEmptyLabel_eq_nonempty : ef.toStatesEmptyLabel = .states (.nonempty) := rfl

@[defeq, simp]
theorem toActionsEmptyLabel_eq_nonempty : ef.toActionsEmptyLabel = .actions (.nonempty) := rfl

section Mk

variable {sts: ωSequence ts.S} {ats: ωSequence ts.Act}

@[defeq, simp]
theorem mk_states : (InfiniteExecutionFragmentRaw.mk sts ats).states = sts := rfl

@[defeq, simp]
theorem mk_actions : (InfiniteExecutionFragmentRaw.mk sts ats).actions = ats := rfl

end Mk

open scoped ωSequence

def stepL (tail: ts.InfiniteExecutionFragmentRaw) (state0: ts.S) (action0: ts.Act) : ts.InfiniteExecutionFragmentRaw :=
  ⟨state0 ::ω tail.states, action0 ::ω tail.actions⟩

section StepL

variable {tl: ts.InfiniteExecutionFragmentRaw} {s0: ts.S} {a0: ts.Act}

@[defeq, simp]
theorem stepL_states : (tl.stepL s0 a0).states = s0 ::ω tl.states := rfl

@[defeq, simp]
theorem stepL_actions : (tl.stepL s0 a0).actions = a0 ::ω tl.actions := rfl

end StepL



def tail (ef: ts.InfiniteExecutionFragmentRaw) : ts.InfiniteExecutionFragmentRaw := ⟨ef.states.tail, ef.actions.tail⟩

section Tail

variable {s0: ts.S} {a0: ts.Act}

@[defeq, simp]
theorem stepL_tail : (ef.stepL s0 a0).tail = ef := by
  cases ef
  rfl

theorem tail_stepL : (ef.tail.stepL (ef.states 0) (ef.actions 0)) = ef := by
  dsimp [tail, stepL]
  simp

end Tail

end InfiniteExecutionFragmentRaw

end Nemonuri.TransitionSystem

end
