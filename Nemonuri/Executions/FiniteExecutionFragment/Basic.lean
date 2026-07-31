module

public import Nemonuri.Executions.FiniteExecutionFragment.Raw

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

structure FiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsFiniteExecutionFragment raw



namespace FiniteExecutionFragment

variable {ts: TransitionSystem} (ϱ: ts.FiniteExecutionFragment)

def states : List ts.S := ϱ.raw.states

def actions : List ts.Act := ϱ.raw.actions

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
theorem states_length_pos : 0 < ϱ.states.length :=
  calc ϱ.states.length
    _ = _ := ϱ.states_length_eq_actions_length_plus_one
    _ > ϱ.actions.length := Nat.lt_add_one _
    _ ≥ 0 := Nat.zero_le _

theorem actions_length_eq_states_length_sub_one : ϱ.actions.length = ϱ.states.length - 1 := by
  simp only [states_length_eq_actions_length_plus_one, Nat.add_sub_cancel]


def refl (state0: ts.S) : ts.FiniteExecutionFragment := mk' [state0] [] (by constructor <;> simp)

theorem refl_actions_length_eq_zero {state0} : (@FiniteExecutionFragment.refl ts state0).actions.length = 0 := by
  dsimp [FiniteExecutionFragment.refl]

def state0 : ts.S := ϱ.states[0]'(ϱ.states_length_pos)


theorem refl_eta (req: ϱ.actions.length = 0) : (refl ϱ.state0) = ϱ := by
  dsimp [FiniteExecutionFragment.refl]
  conv => rhs; rw [← ϱ.mk'_eta]
  congr
  · replace req := congrArg (· + 1) req;
    rewrite [← ϱ.states_length_eq_actions_length_plus_one] at req
    obtain ⟨_, lm1⟩ := List.length_eq_one_iff.mp req
    dsimp [state0]
    simp [lm1]
  · simpa using req

@[defeq, simp]
theorem refl_state0 {state0} : (@FiniteExecutionFragment.refl ts state0).state0 = state0 := by
  dsimp [FiniteExecutionFragment.refl, FiniteExecutionFragment.state0]

theorem stepL_preserves_isFiniteExecutionFragment {state0: ts.S} {action0: ts.Act} (req: state0 ─⌞action0⌟→{ts} ϱ.state0)
  : ts.IsFiniteExecutionFragment ⟨state0 :: ϱ.states, action0 :: ϱ.actions⟩ := by
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

def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ϱ.state0) : FiniteExecutionFragment ts :=
  mk' (state0 :: ϱ.states) (action0 :: ϱ.actions) (ϱ.stepL_preserves_isFiniteExecutionFragment req)

theorem stepL_actions_length_pos {ϱ s act req} : 0 < (@FiniteExecutionFragment.stepL ts ϱ s act req).actions.length := by
  dsimp [FiniteExecutionFragment.stepL]
  rw [← ϱ.states_length_eq_actions_length_plus_one]
  exact ϱ.states_length_pos


theorem tail_preserves_isFiniteExecutionFragment (req: 0 < ϱ.actions.length)
  : ts.IsFiniteExecutionFragment ⟨ϱ.states.tail, ϱ.actions.tail⟩ := by
    constructor
    · simp
      intro i lm1
      refine ϱ.is_valid.states_actions_valid (i+1) ?_
    · simp [states_length_eq_actions_length_plus_one]
      rewrite [Nat.lt_iff_add_one_le] at req
      simp [req]

def tail (req: 0 < ϱ.actions.length) : ts.FiniteExecutionFragment :=
  mk' ϱ.states.tail ϱ.actions.tail (ϱ.tail_preserves_isFiniteExecutionFragment req)

@[defeq, simp]
theorem tail_states {req} : (ϱ.tail req).states = ϱ.states.tail := by dsimp [tail]

@[defeq, simp]
theorem tail_actions {req} : (ϱ.tail req).actions = ϱ.actions.tail := by dsimp [tail]


def action0 (req: 0 < ϱ.actions.length) : ts.Act := ϱ.actions[0]'(req)

--def state1 (req: 0 < ϱ.actions.length) : ts.S := ϱ.states[1]'(by simpa [states_length_eq_actions_length_plus_one] using req)

/-
theorem state1_eq_tail_state0 (req: 0 < ϱ.actions.length)
  : ϱ.state1 req = (ϱ.tail req).state0 := by
  dsimp [FiniteExecutionFragment.state0, FiniteExecutionFragment.state1, FiniteExecutionFragment.tail]
  simp
-/

theorem state0_action0_tail_state0 (req: 0 < ϱ.actions.length)
  : ϱ.state0 ─⌞(ϱ.action0 req)⌟→{ts} (ϱ.tail req).state0 := by
  have lm1 := ϱ.is_valid.states_actions_valid 0 req
  dsimp at lm1
  dsimp [FiniteExecutionFragment.state0, FiniteExecutionFragment.action0, FiniteExecutionFragment.tail]
  simp; exact lm1


theorem stepL_eta (req: 0 < ϱ.actions.length)
  : (stepL (ϱ.tail req) (ϱ.state0) (ϱ.action0 req) (ϱ.state0_action0_tail_state0 req)) = ϱ := by
  dsimp [FiniteExecutionFragment.stepL, FiniteExecutionFragment.tail]
  conv => rhs; rw [← ϱ.mk'_eta]
  congr
  · dsimp [FiniteExecutionFragment.state0]
    simp [List.getElem_zero_eq_head]
  · dsimp [FiniteExecutionFragment.action0]
    simp [List.getElem_zero_eq_head]

@[defeq, simp]
theorem stepL_tail {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).tail stepL_actions_length_pos = tail := by
  dsimp [FiniteExecutionFragment.stepL, FiniteExecutionFragment.tail, mk'_eta]

@[defeq, simp]
theorem stepL_state0 {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).state0 = state0 := by
  dsimp [FiniteExecutionFragment.stepL, FiniteExecutionFragment.state0]

@[defeq, simp]
theorem stepL_action0 {tail state0 action0 req}
  : (@FiniteExecutionFragment.stepL ts tail state0 action0 req).action0 stepL_actions_length_pos = action0 := by
  dsimp [FiniteExecutionFragment.stepL, FiniteExecutionFragment.action0]


@[elab_as_elim]
def indReflStepL
  {motive: ts.FiniteExecutionFragment → Sort _}
  (refl: (state0: ts.S) → motive (FiniteExecutionFragment.refl state0))
  (stepL: (tail : ts.FiniteExecutionFragment) → (state0 : ts.S) → (action0 : ts.Act) → (req: state0 ─⌞action0⌟→{ts} tail.state0) → motive (FiniteExecutionFragment.stepL tail state0 action0 req))
  (t: ts.FiniteExecutionFragment)
  : motive t :=
  if h: t.actions.length = 0 then
    refl t.state0 |> Eq.subst (t.refl_eta h)
  else
    have lm1 := Nat.pos_of_ne_zero h
    stepL (t.tail lm1) t.state0 (t.action0 lm1) (t.state0_action0_tail_state0 lm1) |> Eq.subst (t.stepL_eta lm1)

@[defeq, simp]
theorem indReflStepL_refl {motive refl stepL t} {req: t.actions.length = 0}
  : @indReflStepL ts motive refl stepL t = ((refl t.state0) |> Eq.subst (t.refl_eta req)) :=
  rfl

@[defeq, simp]
theorem indReflStepL_stepL {motive refl stepL t} {req: 0 < t.actions.length}
  : @indReflStepL ts motive refl stepL t = (stepL (t.tail req) t.state0 (t.action0 req) (t.state0_action0_tail_state0 req) |> Eq.subst (t.stepL_eta req)) :=
  rfl


end FiniteExecutionFragment


end Nemonuri.TransitionSystem

end
