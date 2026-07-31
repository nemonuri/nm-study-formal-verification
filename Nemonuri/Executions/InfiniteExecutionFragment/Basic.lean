module

public import Nemonuri.Executions.InfiniteExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem

variable {ts: TransitionSystem}

def IsInfiniteExecutionFragment (raw: ts.InfiniteExecutionFragmentRaw) : Prop := ⦃i: Nat⦄ → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))

namespace IsInfiniteExecutionFragment

theorem mk (raw: ts.InfiniteExecutionFragmentRaw) (x: (i: Nat) → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))) : IsInfiniteExecutionFragment raw := x

theorem apply {raw} (x: ts.IsInfiniteExecutionFragment raw) (i: Nat) : (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1)) := @x i

end IsInfiniteExecutionFragment

@[defeq]
theorem isInfiniteExecutionFragment_eq_omegaExecution (raw: ts.InfiniteExecutionFragmentRaw)
  : ts.IsInfiniteExecutionFragment raw = ts.lts.OmegaExecution raw.states raw.actions :=
  rfl


structure InfiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.InfiniteExecutionFragmentRaw
  is_valid: ts.IsInfiniteExecutionFragment raw




namespace InfiniteExecutionFragment

open Cslib
open scoped ωSequence

variable {ts: TransitionSystem} (ρ: ts.InfiniteExecutionFragment)

def states : ωSequence ts.S := ρ.raw.states

def actions : ωSequence ts.Act := ρ.raw.actions

theorem is_infiniteExecutionFragment : ts.IsInfiniteExecutionFragment ⟨ρ.states, ρ.actions⟩ := ρ.is_valid

def mk' (states: ωSequence ts.S) (actions: ωSequence ts.Act) (req: ts.IsInfiniteExecutionFragment ⟨states, actions⟩) : ts.InfiniteExecutionFragment :=
  ⟨⟨states, actions⟩, req⟩

@[defeq, simp]
theorem mk'_states {states actions req} : (@mk' ts states actions req).states = states := rfl

@[defeq, simp]
theorem mk'_actions {states actions req} : (@mk' ts states actions req).actions = actions := rfl

@[defeq, simp]
theorem mk'_eta : mk' ρ.states ρ.actions ρ.is_infiniteExecutionFragment = ρ := rfl

@[elab_as_elim]
def indMk'
  {motive: ts.InfiniteExecutionFragment → Sort _}
  (mk': (states: ωSequence ts.S) → (actions: ωSequence ts.Act) →
        (req: ts.IsInfiniteExecutionFragment ⟨states, actions⟩) →
        motive (InfiniteExecutionFragment.mk' states actions req))
  (t: ts.InfiniteExecutionFragment)
  : motive t :=
  mk' t.states t.actions t.is_infiniteExecutionFragment |> Eq.subst t.mk'_eta

def state0 := ρ.states 0

def action0 := ρ.actions 0

theorem tail_preserves_isInfiniteExecutionFragment : ts.IsInfiniteExecutionFragment ⟨ρ.states.tail, ρ.actions.tail⟩ := by
  refine IsInfiniteExecutionFragment.mk _ ?_
  dsimp
  intro i
  exact ρ.is_valid.apply (i+1)

def tail : ts.InfiniteExecutionFragment :=
  mk' ρ.states.tail ρ.actions.tail ρ.tail_preserves_isInfiniteExecutionFragment

@[defeq, simp]
theorem tail_states : ρ.tail.states = ρ.states.tail := by dsimp [tail]

@[defeq, simp]
theorem tail_actions : ρ.tail.actions = ρ.actions.tail := by dsimp [tail]


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

def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ρ.state0) : ts.InfiniteExecutionFragment :=
  mk' (state0 ::ω ρ.states) (action0 ::ω ρ.actions) (ρ.stepL_preserves_isInfiniteExecutionFragment req)

@[defeq, simp]
theorem stepL_tail {tail state0 action0 req} : (@stepL ts tail state0 action0 req).tail = tail := rfl

@[defeq, simp]
theorem stepL_state0 {tail state0 action0 req} : (@stepL ts tail state0 action0 req).state0 = state0 := rfl

@[defeq, simp]
theorem stepL_action0 {tail state0 action0 req} : (@stepL ts tail state0 action0 req).action0 = action0 := rfl

theorem tail_canStepL : ρ.state0 ─⌞ρ.action0⌟→{ts} ρ.tail.state0 := by
  dsimp
  have lm1 := @ρ.is_valid 0
  refine Iff.mp ?_ lm1
  rw [← propext_iff]
  congr

theorem stepL_eta : (stepL ρ.tail ρ.state0 ρ.action0 ρ.tail_canStepL) = ρ := by
  dsimp [stepL]
  conv => rhs; rw [← ρ.mk'_eta]
  congr
  · dsimp [state0, tail]; simp only [ωSequence.eta]
  · dsimp [action0, tail]; simp only [ωSequence.eta]

@[elab_as_elim]
def indStepL
  {motive: ts.InfiniteExecutionFragment → Sort _}
  (stepL: (tail: ts.InfiniteExecutionFragment) → (state0: ts.S) → (action0: ts.Act) →
          (req: state0 ─⌞action0⌟→{ts} tail.state0) →
          motive (InfiniteExecutionFragment.stepL tail state0 action0 req))
  (t: ts.InfiniteExecutionFragment)
  : motive t :=
  stepL t.tail t.state0 t.action0 t.tail_canStepL |> Eq.subst t.stepL_eta



end InfiniteExecutionFragment


end Nemonuri.TransitionSystem

end
