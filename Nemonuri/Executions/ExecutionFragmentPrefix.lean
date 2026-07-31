module

public import Nemonuri.Executions.FiniteExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem



structure IsExecutionFragmentPrefix {ts: TransitionSystem} (raw: ts.FiniteExecutionFragmentRaw) : Prop where
  length_eq : raw.states.length = raw.actions.length
  states_actions_valid (i: Nat) (h: i < raw.actions.length - 1) : raw.states[i] ─⌞(raw.actions[i])⌟→{ts} raw.states[i+1]

structure ExecutionFragmentPrefix (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsExecutionFragmentPrefix raw




namespace ExecutionFragmentPrefix

variable {ts: TransitionSystem} (pf: ts.ExecutionFragmentPrefix)

def states : List ts.S := pf.raw.states

def actions : List ts.Act := pf.raw.actions

theorem actions_length_eq_states_length : pf.actions.length = pf.states.length := pf.is_valid.length_eq.symm

def mk' (states : List ts.S) (actions : List ts.Act) (req: ts.IsExecutionFragmentPrefix ⟨states, actions⟩) : ts.ExecutionFragmentPrefix :=
  ⟨⟨states, actions⟩, req⟩

@[defeq]
theorem mk'_eta : mk' pf.states pf.actions pf.is_valid = pf := rfl

@[defeq, simp]
theorem mk'_states {states actions req}
  : (@ExecutionFragmentPrefix.mk' ts states actions req).states = states :=
  rfl

@[defeq, simp]
theorem mk'_actions {states actions req}
  : (@ExecutionFragmentPrefix.mk' ts states actions req).actions = actions :=
  rfl

@[elab_as_elim]
def indMk'
  {motive: ts.ExecutionFragmentPrefix → Sort _}
  (mk': (states : List ts.S) → (actions : List ts.Act) → (req: ts.IsExecutionFragmentPrefix ⟨states, actions⟩) → motive (ExecutionFragmentPrefix.mk' states actions req))
  (t: ts.ExecutionFragmentPrefix)
  : motive t :=
  mk' t.states t.actions t.is_valid |> Eq.subst t.mk'_eta

def nil : ts.ExecutionFragmentPrefix := mk' [] [] (by constructor <;> simp)

@[defeq, simp]
theorem nil_actions_length_eq_zero : (nil : ts.ExecutionFragmentPrefix).actions.length = 0 := rfl

theorem nil_eta (req: pf.actions.length = 0) : (nil : ts.ExecutionFragmentPrefix) = pf := by
  dsimp [ExecutionFragmentPrefix.nil]
  conv => rhs; rw [← pf.mk'_eta]
  congr
  · rewrite [pf.actions_length_eq_states_length] at req
    simpa using req
  · simpa using req



def state0 (req: 0 < pf.actions.length) : ts.S := pf.states[0]'(pf.actions_length_eq_states_length ▸ req)

def action0 (req: 0 < pf.actions.length) : ts.Act := pf.actions[0]'(req)

def CanStepL (state0: ts.S) (action0: ts.Act) : Prop := (h: 0 < pf.actions.length) → (state0 ─⌞action0⌟→{ts} (pf.state0 h))

@[defeq]
theorem canStepL_def {state0 action0} : pf.CanStepL state0 action0 = (∀ (h: 0 < pf.actions.length), (state0 ─⌞action0⌟→{ts} (pf.state0 h))) := rfl

@[simp]
theorem canStepL_actions_length_eq_zero {state0 action0} (req: pf.actions.length = 0)
  : pf.CanStepL state0 action0 := by
  dsimp [canStepL_def]; intro lm1; simp [req] at lm1

theorem canStepL_actions_length_pos_imp_tr {state0 action0} (req: 0 < pf.actions.length) (h: pf.CanStepL state0 action0)
  : state0 ─⌞action0⌟→{ts} (pf.state0 req) := by
  dsimp [canStepL_def] at h
  exact h req


def stepL (state0: ts.S) (action0: ts.Act) (req: pf.CanStepL state0 action0) : ts.ExecutionFragmentPrefix :=
  mk' (state0 :: pf.states) (action0 :: pf.actions) (by
    by_cases lm1: pf.actions.length = 0
    · constructor
      · simp [lm1]
      · simp [lm1]
        rewrite [pf.actions_length_eq_states_length] at lm1
        simpa using lm1
    · replace lm1 := Nat.pos_of_ne_zero lm1
      replace req := pf.canStepL_actions_length_pos_imp_tr lm1 req
      dsimp at req
      constructor
      · dsimp
        intro i lm2
        induction i with
        | zero => dsimp; exact req
        | succ i _ =>
          dsimp
          refine pf.is_valid.states_actions_valid i ?_
          exact Nat.lt_sub_of_add_lt lm2
      · dsimp; rw [pf.actions_length_eq_states_length] )


theorem stepL_actions_length_pos {pf: ts.ExecutionFragmentPrefix} {state0 action0 req} : 0 < (pf.stepL state0 action0 req).actions.length := by
  dsimp [ExecutionFragmentPrefix.stepL]
  simp

def tail : ts.ExecutionFragmentPrefix :=
  mk' pf.states.tail pf.actions.tail (by
    constructor
    · simp
      intro i lm1
      refine pf.is_valid.states_actions_valid (i+1) ?_
      exact Nat.add_lt_of_lt_sub lm1
    · simp; rw [pf.actions_length_eq_states_length] )

@[defeq, simp]
theorem tail_states : pf.tail.states = pf.states.tail := rfl

@[defeq, simp]
theorem tail_actions : pf.tail.actions = pf.actions.tail := rfl


theorem tail_canStepL (req: 0 < pf.actions.length) : pf.tail.CanStepL (pf.state0 req) (pf.action0 req) := by
  dsimp [canStepL_def, ExecutionFragmentPrefix.state0, ExecutionFragmentPrefix.action0]
  simp [-tsub_pos_iff_lt]
  intro lm1
  refine pf.is_valid.states_actions_valid 0 ?_
  exact lm1


theorem stepL_eta (req: 0 < pf.actions.length)
  : (stepL pf.tail (pf.state0 req) (pf.action0 req) (pf.tail_canStepL req)) = pf := by
  dsimp [ExecutionFragmentPrefix.stepL]
  conv => rhs; rw [← pf.mk'_eta]
  congr
  · dsimp [ExecutionFragmentPrefix.state0]
    simp [List.getElem_zero_eq_head]
  · dsimp [ExecutionFragmentPrefix.action0]
    simp [List.getElem_zero_eq_head]

@[defeq, simp]
theorem stepL_tail {tail state0 action0 req}
  : (@stepL ts tail state0 action0 req).tail = tail := by
  dsimp [ExecutionFragmentPrefix.tail, ExecutionFragmentPrefix.stepL]
  exact tail.mk'_eta

@[defeq, simp]
theorem stepL_state0 {tail state0 action0 req}
  : (@stepL ts tail state0 action0 req).state0 stepL_actions_length_pos = state0 := by
  dsimp [ExecutionFragmentPrefix.state0, ExecutionFragmentPrefix.stepL]

@[defeq, simp]
theorem stepL_action0 {tail state0 action0 req}
  : (@stepL ts tail state0 action0 req).action0 stepL_actions_length_pos = action0 := by
  dsimp [ExecutionFragmentPrefix.action0, ExecutionFragmentPrefix.stepL]

@[elab_as_elim]
def indNilStepL
  {motive: ts.ExecutionFragmentPrefix → Sort _}
  (nil: motive (@ExecutionFragmentPrefix.nil ts))
  (stepL: (tail : ts.ExecutionFragmentPrefix) → (state0 : ts.S) → (action0 : ts.Act) → (req : tail.CanStepL state0 action0) → motive (stepL tail state0 action0 req))
  (t: ts.ExecutionFragmentPrefix)
  : motive t :=
  if h: t.actions.length = 0 then
    nil |> Eq.subst (t.nil_eta h)
  else
    have lm1 := Nat.pos_of_ne_zero h
    stepL t.tail (t.state0 lm1) (t.action0 lm1) (t.tail_canStepL lm1) |> Eq.subst (t.stepL_eta lm1)

@[defeq, simp]
theorem indNilStepL_nil (req: pf.actions.length = 0) {motive nil stepL}
  : @indNilStepL ts motive nil stepL pf = (nil |> Eq.subst (pf.nil_eta req)) :=
  rfl

@[defeq, simp]
theorem indNilStepL_stepL (req: 0 < pf.actions.length) {motive nil stepL}
  : @indNilStepL ts motive nil stepL pf = (stepL pf.tail (pf.state0 req) (pf.action0 req) (pf.tail_canStepL req) |> Eq.subst (pf.stepL_eta req)) :=
  rfl


end ExecutionFragmentPrefix



end Nemonuri.TransitionSystem

end
