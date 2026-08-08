module

public import Nemonuri.Executions.InfiniteExecutionFragment.Raws
public import Nemonuri.Executions.FiniteExecutionFragment.Raws

@[expose] public section

namespace Nemonuri.TransitionSystem

open Cslib
open scoped ωSequence

variable {ts: TransitionSystem}

def IsInfiniteExecutionFragment (raw: ts.InfiniteExecutionFragmentRaw) : Prop := ⦃i: Nat⦄ → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))

namespace IsInfiniteExecutionFragment

theorem mk (raw: ts.InfiniteExecutionFragmentRaw) (x: (i: Nat) → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))) : IsInfiniteExecutionFragment raw := x

theorem apply {raw} (x: ts.IsInfiniteExecutionFragment raw) (i: Nat) : (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1)) := @x i

variable {ef: ts.InfiniteExecutionFragmentRaw}

theorem stepL (h: ts.IsInfiniteExecutionFragment ef) (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} (ef.states 0))
  : ts.IsInfiniteExecutionFragment (ef.stepL state0 action0) := by
  refine .mk _ ?_
  intro i
  simp
  rcases i with _ | ⟨n⟩
  · simpa using req
  · simp
    exact h.apply n

theorem tail (h: ts.IsInfiniteExecutionFragment ef) : ts.IsInfiniteExecutionFragment ef.tail := by
  refine .mk _ ?_
  intro i
  simp [InfiniteExecutionFragmentRaw.tail]
  exact h.apply (i+1)

end IsInfiniteExecutionFragment

@[defeq]
theorem isInfiniteExecutionFragment_eq_omegaExecution (raw: ts.InfiniteExecutionFragmentRaw)
  : ts.IsInfiniteExecutionFragment raw = ts.lts.OmegaExecution raw.states raw.actions :=
  rfl

@[ext]
structure InfiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.InfiniteExecutionFragmentRaw
  is_valid: ts.IsInfiniteExecutionFragment raw




namespace InfiniteExecutionFragment

variable {ts: TransitionSystem} (ρ: ts.InfiniteExecutionFragment)

def states : ωSequence ts.S := ρ.raw.states

def actions : ωSequence ts.Act := ρ.raw.actions

--theorem is_infiniteExecutionFragment : ts.IsInfiniteExecutionFragment ⟨ρ.states, ρ.actions⟩ := ρ.is_valid

def mk' (states: ωSequence ts.S) (actions: ωSequence ts.Act) (req: ts.IsInfiniteExecutionFragment ⟨states, actions⟩) : ts.InfiniteExecutionFragment :=
  ⟨⟨states, actions⟩, req⟩

@[defeq, simp]
theorem mk'_states {states actions req} : (@mk' ts states actions req).states = states := rfl

@[defeq, simp]
theorem mk'_actions {states actions req} : (@mk' ts states actions req).actions = actions := rfl

@[defeq, simp]
theorem mk'_eta : mk' ρ.states ρ.actions ρ.is_valid = ρ := rfl

@[elab_as_elim]
def indMk'
  {motive: ts.InfiniteExecutionFragment → Sort _}
  (mk': (states: ωSequence ts.S) → (actions: ωSequence ts.Act) →
        (req: ts.IsInfiniteExecutionFragment ⟨states, actions⟩) →
        motive (InfiniteExecutionFragment.mk' states actions req))
  (t: ts.InfiniteExecutionFragment)
  : motive t :=
  mk' t.states t.actions t.is_valid |> Eq.subst t.mk'_eta

def state0 := ρ.states 0

def action0 := ρ.actions 0

/-
theorem tail_preserves_isInfiniteExecutionFragment : ts.IsInfiniteExecutionFragment ⟨ρ.states.tail, ρ.actions.tail⟩ := by
  refine IsInfiniteExecutionFragment.mk _ ?_
  dsimp
  intro i
  exact ρ.is_valid.apply (i+1)
-/

def tail : ts.InfiniteExecutionFragment := .mk ρ.raw.tail ρ.is_valid.tail

@[defeq, simp]
theorem tail_states : ρ.tail.states = ρ.states.tail := by dsimp [tail]; congr

@[defeq, simp]
theorem tail_actions : ρ.tail.actions = ρ.actions.tail := by dsimp [tail]; congr

@[defeq]
theorem tail_raw : ρ.tail.raw = ρ.raw.tail := rfl

/-
theorem stepL_preserves_isInfiniteExecutionFragment {state0: ts.S} {action0: ts.Act} (req: state0 ─⌞action0⌟→{ts} ρ.state0)
  : ts.IsInfiniteExecutionFragment ⟨state0 ::ω ρ.states, action0 ::ω ρ.actions⟩ := by
    refine IsInfiniteExecutionFragment.mk _ ?_
    dsimp
    intro i
    induction i with
    | zero => exact req
    | succ i ih =>
      simp
      exact ρ.is_valid.apply i
-/

def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ρ.state0) : ts.InfiniteExecutionFragment :=
  .mk (ρ.raw.stepL state0 action0) (ρ.is_valid.stepL state0 action0 req)

section StepL

variable {ρ : ts.InfiniteExecutionFragment} (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ρ.state0)

@[defeq, simp]
theorem stepL_tail : (stepL ρ state0 action0 req).tail = ρ := rfl

@[defeq, simp]
theorem stepL_state0 : (stepL ρ state0 action0 req).state0 = state0 := rfl

@[defeq, simp]
theorem stepL_action0 : (stepL ρ state0 action0 req).action0 = action0 := rfl

@[defeq, simp]
theorem stepL_states : (stepL ρ state0 action0 req).states = state0 ::ω ρ.states := rfl

@[defeq, simp]
theorem stepL_actions : (stepL ρ state0 action0 req).actions = action0 ::ω ρ.actions := rfl

@[defeq]
theorem stepL_raw : (stepL ρ state0 action0 req).raw = (ρ.raw.stepL state0 action0) := rfl

theorem tr_state0_action0_tail_state0 : ρ.state0 ─⌞ρ.action0⌟→{ts} ρ.tail.state0 := by
  dsimp [InfiniteExecutionFragment.state0, InfiniteExecutionFragment.action0]
  exact ρ.is_valid.apply 0



end StepL

theorem stepL_eta : (stepL ρ.tail ρ.state0 ρ.action0 ρ.tr_state0_action0_tail_state0) = ρ := by
  refine InfiniteExecutionFragment.ext ?_
  dsimp [stepL, tail, state0, action0]
  exact InfiniteExecutionFragmentRaw.tail_stepL

  --rcases ρ with ⟨raw, lm1⟩
  --simp [tail_raw, stepL_raw]

/-
  cases ρ using indMk' with
  | mk' sts ats lm1 =>
    dsimp [InfiniteExecutionFragment.stepL, InfiniteExecutionFragment.tail]
    congr
-/
/-
  dsimp [InfiniteExecutionFragment.stepL, InfiniteExecutionFragment.tail]
  congr
  dsimp [InfiniteExecutionFragmentRaw.stepL, InfiniteExecutionFragmentRaw.tail]
  congr
  · dsimp [InfiniteExecutionFragment.state0, InfiniteExecutionFragment.states]; simp
  · dsimp [InfiniteExecutionFragment.action0, InfiniteExecutionFragment.actions]; simp
-/


@[elab_as_elim]
def indStepL
  {motive: ts.InfiniteExecutionFragment → Sort _}
  (stepL: (tail: ts.InfiniteExecutionFragment) → (state0: ts.S) → (action0: ts.Act) →
          (req: state0 ─⌞action0⌟→{ts} tail.state0) →
          motive (InfiniteExecutionFragment.stepL tail state0 action0 req))
  (t: ts.InfiniteExecutionFragment)
  : motive t :=
  stepL t.tail t.state0 t.action0 t.tr_state0_action0_tail_state0 |> Eq.subst t.stepL_eta



end InfiniteExecutionFragment


namespace InfiniteExecutionFragmentRaw

variable {ts: TransitionSystem}

structure IsPrefix (ef1: ts.FiniteExecutionFragmentRaw) (ef2: ts.InfiniteExecutionFragmentRaw) : Prop where
  states: Sequence.IsPrefix ef1.states (.infinite ef2.states)
  actions: Sequence.IsPrefix ef1.actions (.infinite ef2.actions)

end InfiniteExecutionFragmentRaw



end Nemonuri.TransitionSystem

end
