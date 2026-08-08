module

public import Nemonuri.Executions.FiniteExecutionFragment.Raws

@[expose] public section

namespace Nemonuri.TransitionSystem

/-!

### Definition 2.6. Execution Fragment

-/


structure IsFiniteExecutionFragment {ts: TransitionSystem} (raw: ts.FiniteExecutionFragmentRaw) : Prop where
  length_eq : raw.states.length = raw.actions.length + 1
--  firstState_eq : raw.states[0] = raw.firstState
--  lastState_eq : raw.states[raw.states.length - 1] = raw.lastState
  states_actions_valid (i: Nat) (h: i < raw.actions.length) : raw.states[i] ─⌞(raw.actions[i])⌟→{ts} raw.states[i+1]

namespace IsFiniteExecutionFragment

variable {ts: TransitionSystem} {raw: ts.FiniteExecutionFragmentRaw}

@[simp]
theorem singleState {s: ts.S} : IsFiniteExecutionFragment (.singleState s) := by
  constructor <;> simp

open scoped EmptyLabel in
theorem states_nonempty (h: ts.IsFiniteExecutionFragment raw) : EmptyLabel.ofList raw.states = .nonempty := by
  have lm1 := h.length_eq
  cases lm2: raw.states
  · simp [lm2] at lm1
  · dsimp

theorem states_ne_nil (h: ts.IsFiniteExecutionFragment raw) : raw.states ≠ [] :=
  EmptyLabel.ofList_eq_nonempty_iff_ne_nil.mp h.states_nonempty

theorem stepL
  {state0: ts.S} {action0: ts.Act}
  (h: ts.IsFiniteExecutionFragment raw) (req: state0 ─⌞action0⌟→{ts} raw.states[0]'(h.states_ne_nil |> List.length_pos_of_ne_nil))
  : ts.IsFiniteExecutionFragment (raw.stepL state0 action0) := by
  constructor
  · intro i
    simp
    rcases i with _ | n
    · simpa using req
    · simp
      exact h.states_actions_valid n
  · simp
    exact h.length_eq

theorem tail
  (h: ts.IsFiniteExecutionFragment raw) (req: raw.toActionsEmptyLabel.toEmptyLabel = .nonempty)
  : ts.IsFiniteExecutionFragment (raw.tail) := by
  constructor
  · intro i
    simp [FiniteExecutionFragmentRaw.tail]
    rcases i with _ | n
    · simp
      exact h.states_actions_valid 1
    · have lm1 := h.states_actions_valid (n+2)
      dsimp at lm1
      refine (forall_prop_domain_congr ?_ ?_).mp lm1
      · simp
        simp [EmptyLabel.ofList_eq_nonempty_iff_length_pos] at req
        omega
      · simp
  · simp [FiniteExecutionFragmentRaw.tail]
    have lm1 := h.length_eq
    rw [lm1]
    simp [EmptyLabel.ofList_eq_nonempty_iff_length_pos] at req
    omega


end IsFiniteExecutionFragment

@[ext]
structure FiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsFiniteExecutionFragment raw



namespace FiniteExecutionFragment

variable {ts: TransitionSystem} (ϱ: ts.FiniteExecutionFragment)

def states : List ts.S := ϱ.raw.states

def actions : List ts.Act := ϱ.raw.actions

def toSeqLabel : Sequence.Label := ϱ.raw.toSeqLabel

def toStatesEmptyLabel : ExecutionEmptyLabel .states := ϱ.raw.toStatesEmptyLabel

def toActionsEmptyLabel : ExecutionEmptyLabel .actions := ϱ.raw.toActionsEmptyLabel

@[defeq, simp]
theorem toStatesEmptyLabel_eq_ofList {ef: ts.FiniteExecutionFragment} : ef.toStatesEmptyLabel = .states (.ofList ef.states) := rfl

@[defeq, simp]
theorem toActionsEmptyLabel_eq_ofList {ef: ts.FiniteExecutionFragment} : ef.toActionsEmptyLabel = .actions (.ofList ef.actions) := rfl


def mk' (states: List ts.S) (actions: List ts.Act) (req: ts.IsFiniteExecutionFragment ⟨states, actions⟩) : ts.FiniteExecutionFragment :=
  ⟨⟨states, actions⟩, req⟩

@[defeq]
theorem mk'_eta {ϱ: ts.FiniteExecutionFragment} : (mk' ϱ.states ϱ.actions ϱ.is_valid) = ϱ := rfl

@[elab_as_elim]
def indMk'
  {motive: ts.FiniteExecutionFragment → Sort _}
  (mk': (states: List ts.S) → (actions: List ts.Act) → (req: ts.IsFiniteExecutionFragment ⟨states, actions⟩) → motive (FiniteExecutionFragment.mk' states actions req))
  (t: ts.FiniteExecutionFragment)
  : motive t :=
  mk' t.states t.actions t.is_valid |> Eq.subst mk'_eta

@[defeq, simp]
theorem mk'_states {states: List ts.S} {actions req} : (mk' states actions req).states = states := rfl

@[defeq, simp]
theorem mk'_actions {states: List ts.S} {actions req} : (mk' states actions req).actions = actions := rfl

theorem mk'_ext_iff {ϱ1 ϱ2: ts.FiniteExecutionFragment}
  : (ϱ1.states = ϱ2.states ∧ ϱ1.actions = ϱ2.actions) ↔ (ϱ1 = ϱ2) := by
  constructor
  · cases ϱ1 using indMk'
    cases ϱ2 using indMk'
    simp
    intro lm1 lm2
    subst lm1; subst lm2; rfl
  · intro lm1; subst lm1; simp

--def refl' (s: ts.S) : ts.FiniteExecutionFragment := mk' [s] [] (by constructor <;> simp)


theorem states_length_eq_actions_length_plus_one : ϱ.states.length = ϱ.actions.length + 1 := by
  dsimp [FiniteExecutionFragment.states, FiniteExecutionFragment.actions]
  exact ϱ.is_valid.length_eq


@[simp]
theorem states_length_pos : 0 < ϱ.states.length := ϱ.is_valid.states_ne_nil |> List.length_pos_of_ne_nil
/-
  calc ϱ.states.length
    _ = _ := ϱ.states_length_eq_actions_length_plus_one
    _ > ϱ.actions.length := Nat.lt_add_one _
    _ ≥ 0 := Nat.zero_le _
-/

/-
theorem actions_length_eq_states_length_sub_one : ϱ.actions.length = ϱ.states.length - 1 := by
  simp only [states_length_eq_actions_length_plus_one, Nat.add_sub_cancel]
-/

def singleState (state0: ts.S) : ts.FiniteExecutionFragment := .mk (.singleState state0) .singleState

--theorem singleState_

/-
theorem refl_actions_length_eq_zero {state0} : (@FiniteExecutionFragment.refl ts state0).actions.length = 0 := by
  dsimp [FiniteExecutionFragment.refl]
-/

def state0 : ts.S := ϱ.states[0]'(ϱ.states_length_pos)


theorem singleState_eta (req: ϱ.toActionsEmptyLabel.toEmptyLabel = .empty) : (.singleState ϱ.state0) = ϱ := by
  have lm1 := ϱ.states_length_eq_actions_length_plus_one
  simp [EmptyLabel.ofList_eq_empty_iff_eq_nil] at req
  simp [req] at lm1
  dsimp [FiniteExecutionFragment.singleState]
  congr
  refine FiniteExecutionFragmentRaw.ext ?_ ?_
  · dsimp
    dsimp [FiniteExecutionFragment.state0]
    rewrite [List.length_eq_one_iff] at lm1
    obtain ⟨s0, lm1⟩ := lm1
    simp [lm1]; rw [← lm1]; rfl
  · dsimp
    exact req.symm



@[defeq, simp]
theorem singleState_state0 {state0} : (@FiniteExecutionFragment.singleState ts state0).state0 = state0 := by
  dsimp [FiniteExecutionFragment.state0]
  dsimp [FiniteExecutionFragment.singleState]
  congr

/-
theorem stepL_preserves_isFiniteExecutionFragment {state0: ts.S} {action0: ts.Act} (req: state0 ─⌞action0⌟→{ts} ϱ.state0)
  : ts.IsFiniteExecutionFragment (ϱ.raw.stepL state0 action0) := by
    constructor
    · dsimp
      intro i lm1
      induction i with
      | zero =>
        simp
        dsimp [FiniteExecutionFragment.state0] at req
        exact req
      | succ i ih =>
        simp
        refine ϱ.is_valid.states_actions_valid i ?_
    · dsimp
      rw [ϱ.states_length_eq_actions_length_plus_one]
-/

def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ϱ.state0) : FiniteExecutionFragment ts :=
  .mk (ϱ.raw.stepL state0 action0) (ϱ.is_valid.stepL req)

/-
theorem stepL_actions_length_pos {ϱ s act req} : 0 < (@FiniteExecutionFragment.stepL ts ϱ s act req).actions.length := by
  dsimp [FiniteExecutionFragment.stepL]
  rw [← ϱ.states_length_eq_actions_length_plus_one]
  exact ϱ.states_length_pos
-/

/-
theorem tail_preserves_isFiniteExecutionFragment (req: 0 < ϱ.actions.length)
  : ts.IsFiniteExecutionFragment ⟨ϱ.states.tail, ϱ.actions.tail⟩ := by
    constructor
    · simp
      intro i lm1
      refine ϱ.is_valid.states_actions_valid (i+1) ?_
    · simp [states_length_eq_actions_length_plus_one]
      rewrite [Nat.lt_iff_add_one_le] at req
      simp [req]
-/

def tail (req: ϱ.toActionsEmptyLabel.toEmptyLabel = .nonempty) : ts.FiniteExecutionFragment :=
  .mk (ϱ.raw.tail) (ϱ.is_valid.tail req)

@[defeq, simp]
theorem tail_states {req} : (ϱ.tail req).states = ϱ.states.tail := by dsimp [tail]; congr

@[defeq, simp]
theorem tail_actions {req} : (ϱ.tail req).actions = ϱ.actions.tail := by dsimp [tail]; congr


def action0 (req: ϱ.toActionsEmptyLabel.toEmptyLabel = .nonempty) : ts.Act := ϱ.actions[0]'(by simpa [EmptyLabel.ofList_eq_nonempty_iff_length_pos] using req)

--def state1 (req: 0 < ϱ.actions.length) : ts.S := ϱ.states[1]'(by simpa [states_length_eq_actions_length_plus_one] using req)

/-
theorem state1_eq_tail_state0 (req: 0 < ϱ.actions.length)
  : ϱ.state1 req = (ϱ.tail req).state0 := by
  dsimp [FiniteExecutionFragment.state0, FiniteExecutionFragment.state1, FiniteExecutionFragment.tail]
  simp
-/

theorem tr_state0_action0_tail_state0 (req: ϱ.toActionsEmptyLabel.toEmptyLabel = .nonempty)
  : ϱ.state0 ─⌞(ϱ.action0 req)⌟→{ts} (ϱ.tail req).state0 := by
  refine ϱ.is_valid.states_actions_valid 0 ?h1 |> Iff.mp ?_
  case h1 =>
    dsimp [FiniteExecutionFragment.actions] at req
    simpa [EmptyLabel.ofList_eq_nonempty_iff_length_pos] using req
  · dsimp [FiniteExecutionFragment.state0, FiniteExecutionFragment.action0]
    simp
    rfl



theorem stepL_eta (req: ϱ.toActionsEmptyLabel.toEmptyLabel = .nonempty)
  : (stepL (ϱ.tail req) (ϱ.state0) (ϱ.action0 req) (ϱ.tr_state0_action0_tail_state0 req)) = ϱ := by
  refine FiniteExecutionFragment.ext ?_
  dsimp [stepL, tail, state0, action0]
  refine FiniteExecutionFragmentRaw.tail_stepL ?_ ?_


/-
  dsimp [FiniteExecutionFragment.stepL]
  congr
  dsimp [FiniteExecutionFragment.tail]
  dsimp [FiniteExecutionFragmentRaw.tail, FiniteExecutionFragmentRaw.stepL]
  congr
  · dsimp [FiniteExecutionFragment.state0, FiniteExecutionFragment.states]
    simp [List.getElem_zero_eq_head]
  · dsimp [FiniteExecutionFragment.action0, FiniteExecutionFragment.actions]
    simp [List.getElem_zero_eq_head]
-/

section StepL

theorem stepL_toActionsEmptyLabel {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).toActionsEmptyLabel.toEmptyLabel = .nonempty := by
  have lm1 := @tail.raw.stepL_toActionsEmptyLabel ts state0 action0
  simp at lm1
  simp
  exact lm1

@[defeq, simp]
theorem stepL_tail {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).tail stepL_toActionsEmptyLabel = tail :=
  FiniteExecutionFragment.ext tail.raw.stepL_tail

@[defeq, simp]
theorem stepL_state0 {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).state0 = state0 := by
  dsimp [FiniteExecutionFragment.stepL, FiniteExecutionFragment.state0]
  congr

@[defeq, simp]
theorem stepL_action0 {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).action0 stepL_toActionsEmptyLabel = action0 := by
  dsimp [FiniteExecutionFragment.stepL, FiniteExecutionFragment.action0]
  congr

end StepL

@[elab_as_elim]
def indSingleStateStepL
  {motive: ts.FiniteExecutionFragment → Sort _}
  (singleState: (state0: ts.S) → motive (.singleState state0))
  (stepL: (tail : ts.FiniteExecutionFragment) → (state0 : ts.S) → (action0 : ts.Act) → (req: state0 ─⌞action0⌟→{ts} tail.state0) → motive (.stepL tail state0 action0 req))
  (t: ts.FiniteExecutionFragment)
  : motive t :=
  match lm1: t.toActionsEmptyLabel.toEmptyLabel with
  | .empty => singleState t.state0 |> Eq.subst (t.singleState_eta lm1)
  | .nonempty => stepL (t.tail lm1) (t.state0) (t.action0 lm1) (t.tr_state0_action0_tail_state0 lm1) |> Eq.subst (t.stepL_eta lm1)
/-
  if h: t.actions.length = 0 then
    refl t.state0 |> Eq.subst (t.singleState_eta h)
  else
    have lm1 := Nat.pos_of_ne_zero h
    stepL (t.tail lm1) t.state0 (t.action0 lm1) (t.state0_action0_tail_state0 lm1) |> Eq.subst (t.stepL_eta lm1)
-/

@[defeq, simp]
theorem indSingleStateStepL_singleState {motive singleState stepL t} (req: t.toActionsEmptyLabel.toEmptyLabel = .empty)
  : @indSingleStateStepL ts motive singleState stepL t = ((singleState t.state0) |> Eq.subst (t.singleState_eta req)) :=
  rfl

@[defeq, simp]
theorem indSingleStateStepL_stepL {motive singleState stepL t} (req: t.toActionsEmptyLabel.toEmptyLabel = .nonempty)
  : @indSingleStateStepL ts motive singleState stepL t = (stepL (t.tail req) t.state0 (t.action0 req) (t.tr_state0_action0_tail_state0 req) |> Eq.subst (t.stepL_eta req)) :=
  rfl


end FiniteExecutionFragment


namespace FiniteExecutionFragmentRaw

variable {ts: TransitionSystem}

structure IsPrefix (ef1: ts.FiniteExecutionFragmentRaw) (ef2: ts.FiniteExecutionFragmentRaw) : Prop where
  states: List.IsPrefix ef1.states ef2.states
  actions: List.IsPrefix ef1.actions ef2.actions

structure IsSuffix (ef1: ts.FiniteExecutionFragmentRaw) (ef2: ts.FiniteExecutionFragmentRaw) : Prop where
  states: List.IsSuffix ef1.states ef2.states
  actions: List.IsSuffix ef1.actions ef2.actions

end FiniteExecutionFragmentRaw


end Nemonuri.TransitionSystem

end
