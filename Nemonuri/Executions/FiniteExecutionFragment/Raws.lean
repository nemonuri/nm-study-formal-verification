module

public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence
public import Nemonuri.Executions.ExecutionEmptyLabel
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace Nemonuri.TransitionSystem

/-
structure ExecutionLabel where
  states: EmptyLabel
  actions: EmptyLabel
  deriving DecidableEq, Repr

namespace ExecutionLabel

def toProd : ExecutionLabel → (EmptyLabel × EmptyLabel)
  | ⟨l1, l2⟩ => (l1, l2)

def ofProd : (EmptyLabel × EmptyLabel) → ExecutionLabel
  | ⟨l1, l2⟩ => ⟨l1, l2⟩

@[simps]
def equivOfToProd : ExecutionLabel ≃ EmptyLabel × EmptyLabel where
  toFun := toProd
  invFun := ofProd

instance toFintype : Fintype ExecutionLabel := Fintype.ofEquiv (EmptyLabel × EmptyLabel) equivOfToProd.symm

def toEmptyLabel : ExecutionLabel → EmptyLabel
  | ⟨.empty, .empty⟩ => .empty
  | _ => .nonempty


end ExecutionLabel
-/

@[ext]
structure FiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states: List ts.S
  actions: List ts.Act

namespace FiniteExecutionFragmentRaw



variable {ts: TransitionSystem} {ef: ts.FiniteExecutionFragmentRaw}


def toSeqLabel (_: ts.FiniteExecutionFragmentRaw) : Sequence.Label := .finite

def toStatesEmptyLabel (ef: ts.FiniteExecutionFragmentRaw) : ExecutionEmptyLabel .states := .states (.ofList ef.states)

def toActionsEmptyLabel (ef: ts.FiniteExecutionFragmentRaw) : ExecutionEmptyLabel .actions := .actions (.ofList ef.actions)

instance : HasLabel Sequence.Label ts.FiniteExecutionFragmentRaw := ⟨toSeqLabel⟩

instance : HasLabel (ExecutionEmptyLabel .states) ts.FiniteExecutionFragmentRaw := ⟨toStatesEmptyLabel⟩

instance : HasLabel (ExecutionEmptyLabel .actions) ts.FiniteExecutionFragmentRaw := ⟨toActionsEmptyLabel⟩



@[defeq, simp]
theorem toSeqLabel_eq_finite : ef.toSeqLabel = .finite := rfl

@[defeq, simp]
theorem toStatesEmptyLabel_eq_ofList : ef.toStatesEmptyLabel = .states (.ofList ef.states) := rfl

@[defeq, simp]
theorem toActionsEmptyLabel_eq_ofList : ef.toActionsEmptyLabel = .actions (.ofList ef.actions) := rfl

section Mk

variable {sts: List ts.S} {ats: List ts.Act}

@[defeq, simp]
theorem mk_states : (FiniteExecutionFragmentRaw.mk sts ats).states = sts := rfl

@[defeq, simp]
theorem mk_actions : (FiniteExecutionFragmentRaw.mk sts ats).actions = ats := rfl

end Mk


def singleState (s: ts.S) : ts.FiniteExecutionFragmentRaw := ⟨[s], []⟩

section SingleState

variable {s: ts.S}

/-
@[defeq]
theorem singleState_toExecutionLabel : (singleState s).toExecutionLabel = .mk .nonempty .empty := rfl
-/

@[defeq, simp]
theorem singleState_states : (singleState s).states = [s] := rfl

@[defeq, simp]
theorem singleState_actions : (singleState s).actions = [] := rfl

end SingleState



def stepL (tail: ts.FiniteExecutionFragmentRaw) (state0: ts.S) (action0: ts.Act) : ts.FiniteExecutionFragmentRaw :=
  ⟨state0 :: tail.states, action0 :: tail.actions⟩

section StepL

variable {tl: ts.FiniteExecutionFragmentRaw} {s0: ts.S} {a0: ts.Act}

@[defeq, simp]
theorem stepL_states : (tl.stepL s0 a0).states = s0 :: tl.states := rfl

@[defeq, simp]
theorem stepL_actions : (tl.stepL s0 a0).actions = a0 :: tl.actions := rfl

@[defeq, simp]
theorem stepL_toStatesEmptyLabel : (tl.stepL s0 a0).toStatesEmptyLabel.toEmptyLabel = .nonempty := rfl

@[defeq, simp]
theorem stepL_toActionsEmptyLabel : (tl.stepL s0 a0).toActionsEmptyLabel.toEmptyLabel = .nonempty := rfl

end StepL


def tail (ef: ts.FiniteExecutionFragmentRaw) : ts.FiniteExecutionFragmentRaw := ⟨ef.states.tail, ef.actions.tail⟩

section Tail

variable {s0: ts.S} {a0: ts.Act}

@[defeq, simp]
theorem stepL_tail : (ef.stepL s0 a0).tail = ef := by
  cases ef
  rfl

theorem tail_stepL
  --(req1: ef.toStatesEmptyLabel.toEmptyLabel = .nonempty)
  --(req2: ef.toActionsEmptyLabel.toEmptyLabel = .nonempty)
  (req1: 0 < ef.states.length) (req2: 0 < ef.actions.length)
  : ef.tail.stepL (ef.states[0]'(req1)) (ef.actions[0]'(req2)) = ef := by
  dsimp [stepL, tail]
  congr <;> simp [List.getElem_zero_eq_head]

end Tail

end FiniteExecutionFragmentRaw


end Nemonuri.TransitionSystem

end
