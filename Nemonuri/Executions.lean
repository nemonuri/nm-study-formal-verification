module

public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1.1 Executions, p.24

-/


@[expose] public section

namespace Nemonuri.TransitionSystem

/-!

### Definition 2.6. Execution Fragment

-/

section Definition

variable {ts: TransitionSystem}

structure FiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states: List ts.S
  actions: List ts.Act

structure IsFiniteExecutionFragment (raw: ts.FiniteExecutionFragmentRaw) : Prop where
  length_eq : raw.states.length = raw.actions.length + 1
--  firstState_eq : raw.states[0] = raw.firstState
--  lastState_eq : raw.states[raw.states.length - 1] = raw.lastState
  states_actions_valid (i: Nat) (h: i < raw.actions.length) : raw.states[i] ─⌞(raw.actions[i])⌟→{ts} raw.states[i+1]

structure FiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsFiniteExecutionFragment raw

end Definition

/-
namespace FiniteExecutionFragmentRaw

variable {ts: TransitionSystem} (raw: ts.FiniteExecutionFragmentRaw)

def statesLength : Nat := raw.states.length

def actionsLength : Nat := raw.actions.length

def minLength : Nat := Nat.min raw.states.length raw.actions.length

theorem lt_minLength_iff (i: Nat) : (i < raw.minLength) ↔ ((i < raw.statesLength) ∧ (i < raw.actionsLength)) :=
  Nat.lt_min


theorem lt_minLength_imp_lt_states_length (i: Nat) (h: i < raw.minLength) : i < raw.statesLength :=
  raw.lt_minLength_iff i |>.mp h |>.left

theorem lt_minLength_imp_lt_actions_length (i: Nat) (h: i < raw.minLength) : i < raw.actionsLength :=
  raw.lt_minLength_iff i |>.mp h |>.right


def getStateAt (i: Nat) (req: i < raw.statesLength) : ts.S := raw.states[i]'(req)

def getActionAt (i: Nat) (req: i < raw.actionsLength) : ts.Act := raw.actions[i]'(req)


end FiniteExecutionFragmentRaw
-/



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



def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ϱ.state0) : FiniteExecutionFragment ts :=
  mk' (state0 :: ϱ.states) (action0 :: ϱ.actions) (by
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
      rw [ϱ.states_length_eq_actions_length_plus_one] )

theorem stepL_actions_length_pos {ϱ s act req} : 0 < (@FiniteExecutionFragment.stepL ts ϱ s act req).actions.length := by
  dsimp [FiniteExecutionFragment.stepL]
  rw [← ϱ.states_length_eq_actions_length_plus_one]
  exact ϱ.states_length_pos

def tail (req: 0 < ϱ.actions.length) : ts.FiniteExecutionFragment :=
  mk' ϱ.states.tail ϱ.actions.tail (by
    constructor
    · simp
      intro i lm1
      refine ϱ.is_valid.states_actions_valid (i+1) ?_
    · simp [states_length_eq_actions_length_plus_one]
      rewrite [Nat.lt_iff_add_one_le] at req
      simp [req] )

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

section Notation




end Notation


end FiniteExecutionFragment


section Definition

variable {ts: TransitionSystem}


structure IsExecutionFragmentPrefix (raw: ts.FiniteExecutionFragmentRaw) : Prop where
  length_eq : raw.states.length = raw.actions.length
  states_actions_valid (i: Nat) (h: i < raw.actions.length - 1) : raw.states[i] ─⌞(raw.actions[i])⌟→{ts} raw.states[i+1]

structure ExecutionFragmentPrefix (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsExecutionFragmentPrefix raw

end Definition


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




section Definition

variable {ts: TransitionSystem}

structure IsExecutionFragmentPostfix (raw: ts.FiniteExecutionFragmentRaw) : Prop where
  length_eq : raw.states.length = raw.actions.length
  states_actions_valid (i: Nat) (h: i < raw.actions.length - 1) : raw.states[i] ─⌞(raw.actions[i+1])⌟→{ts} raw.states[i+1]

structure ExecutionFragmentPostfix (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsExecutionFragmentPostfix raw

end Definition

namespace ExecutionFragmentPostfix


variable {ts: TransitionSystem} (pf: ts.ExecutionFragmentPostfix)

def states : List ts.S := pf.raw.states

def actions : List ts.Act := pf.raw.actions

theorem actions_length_eq_states_length : pf.actions.length = pf.states.length := pf.is_valid.length_eq.symm

def mk' (states : List ts.S) (actions : List ts.Act) (req: ts.IsExecutionFragmentPostfix ⟨states, actions⟩) : ts.ExecutionFragmentPostfix :=
  ⟨⟨states, actions⟩, req⟩


@[defeq]
theorem mk'_eta : mk' pf.states pf.actions pf.is_valid = pf := rfl

@[defeq, simp]
theorem mk'_states {states actions req}
  : (@ExecutionFragmentPostfix.mk' ts states actions req).states = states :=
  rfl

@[defeq, simp]
theorem mk'_actions {states actions req}
  : (@ExecutionFragmentPostfix.mk' ts states actions req).actions = actions :=
  rfl

@[elab_as_elim]
def indMk'
  {motive: ts.ExecutionFragmentPostfix → Sort _}
  (mk': (states : List ts.S) → (actions : List ts.Act) → (req: ts.IsExecutionFragmentPostfix ⟨states, actions⟩) → motive (ExecutionFragmentPostfix.mk' states actions req))
  (t: ts.ExecutionFragmentPostfix)
  : motive t :=
  mk' t.states t.actions t.is_valid |> Eq.subst t.mk'_eta

def nil : ts.ExecutionFragmentPostfix := mk' [] [] (by constructor <;> simp)


@[defeq, simp]
theorem nil_actions_length_eq_zero : (nil : ts.ExecutionFragmentPostfix).actions.length = 0 := rfl

theorem nil_eta (req: pf.actions.length = 0) : (nil : ts.ExecutionFragmentPostfix) = pf := by
  dsimp [ExecutionFragmentPostfix.nil]
  conv => rhs; rw [← pf.mk'_eta]
  congr
  · rewrite [pf.actions_length_eq_states_length] at req
    simpa using req
  · simpa using req



def state0 (req: 0 < pf.actions.length) : ts.S := pf.states[0]'(pf.actions_length_eq_states_length ▸ req)

def action0 (req: 0 < pf.actions.length) : ts.Act := pf.actions[0]'(req)

def CanStepL (state0: ts.S) : Prop := (h: 0 < pf.actions.length) → (state0 ─⌞(pf.action0 h)⌟→{ts} (pf.state0 h))

@[defeq]
theorem canStepL_def {state0} : pf.CanStepL state0 = (∀ (h: 0 < pf.actions.length), (state0 ─⌞(pf.action0 h)⌟→{ts} (pf.state0 h))) := rfl

@[simp]
theorem canStepL_actions_length_eq_zero {state0} (req: pf.actions.length = 0)
  : pf.CanStepL state0 := by
  dsimp [canStepL_def]; intro lm1; simp [req] at lm1

theorem canStepL_actions_length_pos_imp_tr {state0} (req: 0 < pf.actions.length) (h: pf.CanStepL state0)
  : state0 ─⌞(pf.action0 req)⌟→{ts} (pf.state0 req) := by
  dsimp [canStepL_def] at h
  exact h req


def stepL (state0: ts.S) (action0: ts.Act) (req: pf.CanStepL state0) : ts.ExecutionFragmentPostfix :=
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


theorem stepL_actions_length_pos {pf: ts.ExecutionFragmentPostfix} {state0 action0 req} : 0 < (pf.stepL state0 action0 req).actions.length := by
  dsimp [ExecutionFragmentPostfix.stepL]
  simp

def tail : ts.ExecutionFragmentPostfix :=
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


theorem tail_canStepL (req: 0 < pf.actions.length) : pf.tail.CanStepL (pf.state0 req) := by
  dsimp [canStepL_def, ExecutionFragmentPostfix.state0, ExecutionFragmentPostfix.action0]
  simp [-tsub_pos_iff_lt]
  intro lm1
  refine pf.is_valid.states_actions_valid 0 ?_
  exact lm1


theorem stepL_eta (req: 0 < pf.actions.length)
  : (stepL pf.tail (pf.state0 req) (pf.action0 req) (pf.tail_canStepL req)) = pf := by
  dsimp [ExecutionFragmentPostfix.stepL]
  conv => rhs; rw [← pf.mk'_eta]
  congr
  · dsimp [ExecutionFragmentPostfix.state0]
    simp [List.getElem_zero_eq_head]
  · dsimp [ExecutionFragmentPostfix.action0]
    simp [List.getElem_zero_eq_head]

@[defeq, simp]
theorem stepL_tail {tail state0 action0 req}
  : (@stepL ts tail state0 action0 req).tail = tail := by
  dsimp [ExecutionFragmentPostfix.tail, ExecutionFragmentPostfix.stepL]
  exact tail.mk'_eta

@[defeq, simp]
theorem stepL_state0 {tail state0 action0 req}
  : (@stepL ts tail state0 action0 req).state0 stepL_actions_length_pos = state0 := by
  dsimp [ExecutionFragmentPostfix.state0, ExecutionFragmentPostfix.stepL]

@[defeq, simp]
theorem stepL_action0 {tail state0 action0 req}
  : (@stepL ts tail state0 action0 req).action0 stepL_actions_length_pos = action0 := by
  dsimp [ExecutionFragmentPostfix.action0, ExecutionFragmentPostfix.stepL]

@[elab_as_elim]
def indNilStepL
  {motive: ts.ExecutionFragmentPostfix → Sort _}
  (nil: motive (@ExecutionFragmentPostfix.nil ts))
  (stepL: (tail : ts.ExecutionFragmentPostfix) → (state0 : ts.S) → (action0 : ts.Act) → (req : tail.CanStepL state0) → motive (stepL tail state0 action0 req))
  (t: ts.ExecutionFragmentPostfix)
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


end ExecutionFragmentPostfix



section Definition

open Cslib

variable {ts: TransitionSystem}

structure InfiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states : ωSequence ts.S
  actions : ωSequence ts.Act

def IsInfiniteExecutionFragment (raw: ts.InfiniteExecutionFragmentRaw) : Prop := ⦃i: Nat⦄ → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))

namespace IsInfiniteExecutionFragment

theorem mk (raw: ts.InfiniteExecutionFragmentRaw) (x: (i: Nat) → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))) : IsInfiniteExecutionFragment raw := x

theorem apply {raw} (x: ts.IsInfiniteExecutionFragment raw) (i: Nat) : (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1)) := @x i

end IsInfiniteExecutionFragment

/-
@[defeq]
theorem isInfiniteExecutionFragment_def (raw: ts.InfiniteExecutionFragmentRaw)
  : IsInfiniteExecutionFragment raw = ((i: Nat) → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1))) :=
  rfl
-/

@[defeq]
theorem isInfiniteExecutionFragment_eq_omegaExecution (raw: ts.InfiniteExecutionFragmentRaw)
  : ts.IsInfiniteExecutionFragment raw = ts.lts.OmegaExecution raw.states raw.actions :=
  rfl


structure InfiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.InfiniteExecutionFragmentRaw
  is_valid: ts.IsInfiniteExecutionFragment raw

/-| The term `execution fragment` will be used to denote either a finite or an infinite execution fragment -/
/-
inductive ExecutionFragment (ts: TransitionSystem) where
  | finite (ϱ: ts.FiniteExecutionFragment) : ExecutionFragment ts
  | infinite (ρ: ts.InfiniteExecutionFragment) : ExecutionFragment ts
-/

end Definition

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

def tail : ts.InfiniteExecutionFragment :=
  mk' ρ.states.tail ρ.actions.tail (by
    refine IsInfiniteExecutionFragment.mk _ ?_
    dsimp
    intro i
    exact ρ.is_valid.apply (i+1) )

def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ρ.state0) : ts.InfiniteExecutionFragment :=
  mk' (state0 ::ω ρ.states) (action0 ::ω ρ.actions) (by
    refine IsInfiniteExecutionFragment.mk _ ?_
    dsimp
    intro i
    induction i with
    | zero => exact req
    | succ i ih =>
      simp
      exact ρ.is_valid.apply i )

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



inductive ExecutionFragmentRaw (ts: TransitionSystem) where
  | finite (ϱ: ts.FiniteExecutionFragmentRaw)
  | infinite (ρ: ts.InfiniteExecutionFragmentRaw)

namespace ExecutionFragmentRaw

variable {ts: TransitionSystem} {raw: ts.ExecutionFragmentRaw}


def states : ts.ExecutionFragmentRaw → Sequence ts.S
  | .finite ϱ => .finite ϱ.states
  | .infinite ρ => .infinite ρ.states

@[defeq, simp]
theorem finite_states {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).states = (.finite ϱ.states) := rfl

@[defeq, simp]
theorem infinite_states {ρ} : (@ExecutionFragmentRaw.infinite ts ρ).states = (.infinite ρ.states) := rfl


def actions : ts.ExecutionFragmentRaw → Sequence ts.Act
  | .finite ϱ => .finite ϱ.actions
  | .infinite ρ => .infinite ρ.actions

@[defeq, simp]
theorem finite_actions {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).actions = (.finite ϱ.actions) := rfl

@[defeq, simp]
theorem infinite_actions {ρ} : (@ExecutionFragmentRaw.infinite ts ρ).actions = (.infinite ρ.actions) := rfl


theorem states_isFinite_eq_actions_isFinite (raw: ts.ExecutionFragmentRaw) : raw.states.isFinite = raw.actions.isFinite := by
  dsimp [states, actions]
  cases raw <;> simp



def ofSequence
  (states: Sequence ts.S) (actions: Sequence ts.Act) (req: states.isFinite = actions.isFinite) : ts.ExecutionFragmentRaw :=
  match states, actions with
  | .finite xs1, .finite xs2 => .finite ⟨xs1, xs2⟩
  | .infinite xs1, .infinite xs2 => .infinite ⟨xs1, xs2⟩

@[simp]
theorem ofSequence_states {states: Sequence ts.S} {actions req}
  : (ofSequence states actions req).states = states := by
  dsimp [ofSequence]
  cases states <;> cases actions <;> simp at req <;> dsimp

@[simp]
theorem ofSequence_actions {states: Sequence ts.S} {actions req}
  : (ofSequence states actions req).actions = actions := by
  dsimp [ofSequence]
  cases states <;> cases actions <;> simp at req <;> simp


theorem ofSequence_eta
  : (ofSequence raw.states raw.actions raw.states_isFinite_eq_actions_isFinite) = raw := by
  dsimp [ExecutionFragmentRaw.ofSequence, states, actions]
  cases raw <;> simp


@[elab_as_elim]
def indOfSequence
  {motive: ts.ExecutionFragmentRaw → Sort _}
  (ofSequence: (states: Sequence ts.S) → (actions: Sequence ts.Act) → (req: states.isFinite = actions.isFinite) → motive (ExecutionFragmentRaw.ofSequence states actions req))
  (t: ts.ExecutionFragmentRaw)
  : motive t :=
  ofSequence t.states t.actions t.states_isFinite_eq_actions_isFinite |> Eq.subst ofSequence_eta

theorem ofSequence_ext_iff {raw1 raw2: ts.ExecutionFragmentRaw}
  : (raw1.states = raw2.states) ∧ (raw1.actions = raw2.actions) ↔ raw1 = raw2 := by
  constructor
  · cases raw1 using indOfSequence
    cases raw2 using indOfSequence
    simp
    intro lm1 lm2
    subst lm1; subst lm2; rfl
  · intro lm1; subst lm1; simp



def isFinite : ts.ExecutionFragmentRaw → Bool
  | .finite _ => .true
  | .infinite _ => .false

@[simp, grind =]
theorem isFinite_finite {ϱ: ts.FiniteExecutionFragmentRaw} : isFinite (.finite ϱ) = .true := rfl

@[simp, grind =]
theorem isFinite_infinite {ρ: ts.InfiniteExecutionFragmentRaw} : isFinite (.infinite ρ) = .false := rfl

def getFinite (raw: ts.ExecutionFragmentRaw) (req: raw.isFinite) : ts.FiniteExecutionFragmentRaw :=
  match raw with
  | .finite xs => xs
  | .infinite _ => absurd req (by simp)

@[defeq, simp]
theorem finite_getFinite {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).getFinite isFinite_finite = ϱ := rfl


def isInfinite : ts.ExecutionFragmentRaw → Bool
  | .finite _ => .false
  | .infinite _ => .true

@[simp, grind =]
theorem isInfinite_finite {ϱ: ts.FiniteExecutionFragmentRaw} : isInfinite (.finite ϱ) = .false := rfl

@[simp, grind =]
theorem isInfinite_infinite {ρ: ts.InfiniteExecutionFragmentRaw} : isInfinite (.infinite ρ) = .true := rfl

def getInfinite (raw: ts.ExecutionFragmentRaw) (req: raw.isInfinite) : ts.InfiniteExecutionFragmentRaw :=
  match raw with
  | .finite _ => absurd req (by simp)
  | .infinite xs => xs

@[defeq, simp]
theorem infinite_getInfinite {ρ} : (@ExecutionFragmentRaw.infinite ts ρ).getInfinite isInfinite_infinite = ρ := rfl


@[simp, grind =]
theorem not_isFinite_eq_isInfinite
  : (!raw.isFinite) = raw.isInfinite := by
  cases raw <;> simp

@[simp, grind =]
theorem not_isInfinite_eq_isFinite
  : (!raw.isInfinite) = raw.isFinite := by
  cases raw <;> simp

@[simp]
theorem isFinite_eq_false_iff
  : raw.isFinite = .false ↔ raw.isInfinite = .true := by
  cases raw <;> simp

@[simp]
theorem isInfinite_eq_false_iff
  : raw.isInfinite = .false ↔ raw.isFinite = .true := by
  cases raw <;> simp



theorem isFinite_eq_states_isFinite : raw.isFinite = raw.states.isFinite := by
  cases raw <;> simp

@[defeq, simp]
theorem ofSequence_finite_isFinite {sts ats} : (@ofSequence ts (.finite sts) (.finite ats) rfl).isFinite = .true := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_finite_isInFinite {sts ats} : (@ofSequence ts (.finite sts) (.finite ats) rfl).isInfinite = .false := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_infinite_isInFinite {sts ats} : (@ofSequence ts (.infinite sts) (.infinite ats) rfl).isInfinite = .true := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_infinite_isFinite {sts ats} : (@ofSequence ts (.infinite sts) (.infinite ats) rfl).isFinite = .false := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_finite_getFinite {sts ats}
  : (@ofSequence ts (.finite sts) (.finite ats) rfl).getFinite ofSequence_finite_isFinite = ⟨sts, ats⟩ := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_infinite_getInfinite {sts ats}
  : (@ofSequence ts (.infinite sts) (.infinite ats) rfl).getInfinite ofSequence_infinite_isInFinite = ⟨sts, ats⟩ := by
  dsimp [ofSequence]


theorem IsPrefix.lt_aux {n1 n2: Nat} {en: ENat} (h1: n1 < n2) (h2: Nat.cast n2 < en) : Nat.cast n1 < en :=
  calc
    _ < _ := ENat.coe_lt_coe.mpr h1
    _ < _ := h2


structure IsPrefix (raw: ts.ExecutionFragmentRaw) (pf: ts.FiniteExecutionFragmentRaw) : Prop where
  states_length_lt: pf.states.length < raw.states.length?
  states_prefix (i: Nat) (req: i < pf.states.length) : (pf.states[i]'(req)) = (raw.states[i]'(IsPrefix.lt_aux req states_length_lt))
  actions_length_lt: pf.actions.length < raw.actions.length?
  actions_prefix (i: Nat) (req: i < pf.actions.length) : (pf.actions[i]'(req)) = (raw.actions[i]'(IsPrefix.lt_aux req actions_length_lt))


theorem _root_.Nat.gt_imp_pos {n1 n2: Nat} (h: n1 < n2) : 0 < n2 := by
  induction n1 with
  | zero => exact h
  | succ n _ =>
    calc
      0 < 1 := Nat.zero_lt_one
      _ ≤ _ := Nat.le_add_left _ n
      _ < _ := h


theorem IsPostfix.lt_aux {n: Nat} {m: ENat} {i: Nat} (req1: i < n) (req2: n < m.toNat)
  : (m.toNat - n + i) < m :=
  calc
    m ≥ m.toNat := m.coe_toNat_le_self
    _ > Nat.cast (m.toNat - (n - i)) := Nat.sub_lt (Nat.gt_imp_pos req2) (Nat.zero_lt_sub_of_lt req1) |> ENat.coe_lt_coe.mpr
    _ = Nat.cast (m.toNat - n + i) := ENat.coe_inj.mpr (by omega)


structure IsPostfix (raw: ts.ExecutionFragmentRaw) (pf: ts.FiniteExecutionFragmentRaw) : Prop where
  states_length_lt: pf.states.length < raw.states.length?.toNat
  states_postfix (i: Nat) (req: i < pf.states.length) :
    (pf.states[i]'(req)) = (raw.states[raw.states.length?.toNat - pf.states.length + i]'(IsPostfix.lt_aux req states_length_lt))
  actions_length_lt: pf.actions.length < raw.actions.length?.toNat
  actions_postfix (i: Nat) (req: i < pf.actions.length) :
    (pf.actions[i]'(req)) = (raw.actions[raw.actions.length?.toNat - pf.actions.length + i]'(IsPostfix.lt_aux req actions_length_lt))

@[simp]
theorem infinite_not_isPostfix {ρ} {pf} : ¬(@ExecutionFragmentRaw.infinite ts ρ).IsPostfix pf := by
  intro lm1
  have lm2 := lm1.states_length_lt
  simp at lm2

theorem isPostfix_imp_isFinite {pf} (h: raw.IsPostfix pf) : raw.isFinite := by
  cases raw
  · simp
  · simp at h

structure ArePrefixAndPostfix (raw: ts.ExecutionFragmentRaw) (pref: ts.FiniteExecutionFragmentRaw) (postf: ts.FiniteExecutionFragmentRaw) : Prop where
  is_prefix: raw.IsPrefix pref
  is_postfix: raw.IsPostfix postf
  states_not_overlap: pref.states.length + postf.states.length ≤ raw.states.length?.toNat
  actions_not_overlap: pref.actions.length + postf.actions.length ≤ raw.actions.length?.toNat

@[simp]
theorem infinite_not_arePrefixAndPostfix {ρ pref postf} : ¬(@ExecutionFragmentRaw.infinite ts ρ).ArePrefixAndPostfix pref postf := by
  intro lm1
  have lm2 := lm1.is_postfix
  simp at lm2

theorem arePrefixAndPostfix_imp_isFinite {pref postf} (h: raw.ArePrefixAndPostfix pref postf) : raw.isFinite := h.is_postfix |> isPostfix_imp_isFinite


end ExecutionFragmentRaw

/-
inductive ExecutionFragmentRaw (ts: TransitionSystem) where
  | finite (ϱ: ts.FiniteExecutionFragmentRaw)
  | infinite (ρ: ts.InfiniteExecutionFragmentRaw)
-/

section Definition

variable {ts: TransitionSystem}


inductive IsExecutionFragment (raw: ts.ExecutionFragmentRaw) : Prop where
  | finite (req1: raw.isFinite) (req2: IsFiniteExecutionFragment (raw.getFinite req1))
  | infinite (req1: raw.isInfinite) (req2: IsInfiniteExecutionFragment (raw.getInfinite req1))

structure ExecutionFragment (ts: TransitionSystem) where
  raw: ts.ExecutionFragmentRaw
  is_valid: ts.IsExecutionFragment raw


end Definition


namespace ExecutionFragment

variable {ts: TransitionSystem} (ef: ts.ExecutionFragment)

def states : Sequence ts.S := ef.raw.states

def actions : Sequence ts.Act := ef.raw.actions

theorem states_isFinite_eq_actions_isFinite : ef.states.isFinite = ef.actions.isFinite := ExecutionFragmentRaw.states_isFinite_eq_actions_isFinite _

theorem is_executionFragment : IsExecutionFragment (.ofSequence ef.states ef.actions ef.states_isFinite_eq_actions_isFinite) := by
  dsimp [ExecutionFragment.states, ExecutionFragment.actions]
  rw [ef.raw.ofSequence_eta]
  exact ef.is_valid

def mk'
  (states : Sequence ts.S) (actions : Sequence ts.Act)
  (req1: states.isFinite = actions.isFinite)
  (req2: IsExecutionFragment (.ofSequence states actions req1) )
  : ts.ExecutionFragment :=
  ⟨ExecutionFragmentRaw.ofSequence states actions req1, req2⟩

theorem mk'_eta
  : (mk' ef.states ef.actions ef.states_isFinite_eq_actions_isFinite ef.is_executionFragment) = ef := by
  dsimp [mk']
  dsimp [ExecutionFragment.states, ExecutionFragment.actions]
  simp only [ef.raw.ofSequence_eta]

@[simp]
theorem mk'_states {states actions req1 req2}
  : (@ExecutionFragment.mk' ts states actions req1 req2).states = states := by
  dsimp [ExecutionFragment.mk', ExecutionFragment.states]
  simp

@[simp]
theorem mk'_actions {states actions req1 req2}
  : (@ExecutionFragment.mk' ts states actions req1 req2).actions = actions := by
  dsimp [ExecutionFragment.mk', ExecutionFragment.actions]
  simp

@[elab_as_elim]
def indMk'
  {motive : ts.ExecutionFragment → Sort _}
  (mk': (states : Sequence ts.S) → (actions : Sequence ts.Act) →
        (req1: states.isFinite = actions.isFinite) →
        (req2: IsExecutionFragment (.ofSequence states actions req1)) →
        motive (ExecutionFragment.mk' states actions req1 req2))
  (t: ts.ExecutionFragment)
  : motive t :=
  mk' t.states t.actions t.states_isFinite_eq_actions_isFinite t.is_executionFragment |> Eq.subst t.mk'_eta


def isFinite : Bool := ef.raw.isFinite

def isInfinite : Bool := ef.raw.isInfinite

@[simp]
theorem isFinite_eq_false_iff : ef.isFinite = .false ↔ ef.isInfinite = .true := by
  dsimp [isFinite, isInfinite]
  simp only [ExecutionFragmentRaw.isFinite_eq_false_iff]

@[simp]
theorem isInfinite_eq_false_iff : ef.isInfinite = .false ↔ ef.isFinite = .true := by
  dsimp [isFinite, isInfinite]
  simp only [ExecutionFragmentRaw.isInfinite_eq_false_iff]


def ofFinite (ϱ: ts.FiniteExecutionFragment) : ts.ExecutionFragment :=
  ⟨.finite ϱ.raw, (by
    open ExecutionFragmentRaw in
    refine IsExecutionFragment.finite ?_ ?_
    · dsimp only [isFinite_finite]
    · dsimp only [finite_getFinite]
      exact ϱ.is_valid )⟩

@[defeq, simp]
theorem ofFinite_isFinite {ϱ} : (@ofFinite ts ϱ).isFinite = .true := by
  dsimp [ofFinite, isFinite]

def getFinite (req: ef.isFinite) : ts.FiniteExecutionFragment :=
  ⟨ef.raw.getFinite req, (by
    cases ef.is_valid
    · assumption
    · refine absurd req ?_
      simp [isFinite]
      assumption )⟩

@[defeq, simp]
theorem ofFinite_getFinite {ϱ} : (@ofFinite ts ϱ).getFinite ofFinite_isFinite = ϱ := rfl

theorem ofFinite_eta (req: ef.isFinite) : (ofFinite (ef.getFinite req)) = ef := by
  rcases ef with ⟨raw, is_valid⟩
  cases raw
  · congr
  · dsimp [ExecutionFragment.isFinite] at req
    contradiction

@[defeq, simp]
theorem ofFinite_states {ϱ} : (@ofFinite ts ϱ).states = (.finite ϱ.states) := rfl

@[defeq, simp]
theorem ofFinite_actions {ϱ} : (@ofFinite ts ϱ).actions = (.finite ϱ.actions) := rfl



def ofInfinite (ρ: ts.InfiniteExecutionFragment) : ts.ExecutionFragment :=
  ⟨.infinite ρ.raw, (by
    open ExecutionFragmentRaw in
    refine IsExecutionFragment.infinite ?_ ?_
    · dsimp only [isInfinite_infinite]
    · dsimp only [infinite_getInfinite]
      exact ρ.is_valid )⟩

@[defeq, simp]
theorem ofInfinite_isInfinite {ρ} : (@ofInfinite ts ρ).isInfinite = .true := by
  dsimp [ofInfinite, isInfinite]

def getInfinite (req: ef.isInfinite) : ts.InfiniteExecutionFragment :=
  ⟨ef.raw.getInfinite req, (by
    cases ef.is_valid
    · refine absurd req ?_
      simp [isInfinite]
      assumption
    · assumption )⟩

@[defeq, simp]
theorem ofInfinite_getInfinite {ρ} : (@ofInfinite ts ρ).getInfinite ofInfinite_isInfinite = ρ := rfl

theorem ofInfinite_eta (req: ef.isInfinite) : (ofInfinite (ef.getInfinite req)) = ef := by
  rcases ef with ⟨raw, is_valid⟩
  cases raw
  · dsimp [ExecutionFragment.isInfinite] at req
    contradiction
  · congr

@[defeq, simp]
theorem ofInfinite_states {ρ} : (@ofInfinite ts ρ).states = (.infinite ρ.states) := rfl

@[defeq, simp]
theorem ofInfinite_actions {ρ} : (@ofInfinite ts ρ).actions = (.infinite ρ.actions) := rfl


@[elab_as_elim]
def indFiniteInfinite
  {motive: ts.ExecutionFragment → Sort _}
  (finite: (ϱ: ts.FiniteExecutionFragment) → motive (ofFinite ϱ))
  (infinite: (ρ: ts.InfiniteExecutionFragment) → motive (ofInfinite ρ))
  (t: ts.ExecutionFragment)
  : motive t :=
  if lm1: t.isFinite then
    finite (t.getFinite lm1) |> Eq.subst (t.ofFinite_eta lm1)
  else
    have lm2 := t.isFinite_eq_false_iff.mp (Bool.of_not_eq_true lm1)
    infinite (t.getInfinite lm2) |> Eq.subst (t.ofInfinite_eta lm2)

@[defeq, simp]
theorem isFinite_indFiniteInfinite (req: ef.isFinite) {motive finite infinite}
  : @indFiniteInfinite ts motive finite infinite ef = (finite (ef.getFinite req) |> Eq.subst (ef.ofFinite_eta req)) :=
  rfl

@[defeq, simp]
theorem isInfinite_indFiniteInfinite (req: ef.isInfinite) {motive finite infinite}
  : @indFiniteInfinite ts motive finite infinite ef = (infinite (ef.getInfinite req) |> Eq.subst (ef.ofInfinite_eta req)) :=
  rfl

theorem states_length?_eq_actions_length?_plus_one : ef.states.length? = ef.actions.length? + 1 := by
  cases ef using indFiniteInfinite with
  | finite ϱ =>
    have lm1 := ϱ.states_length_eq_actions_length_plus_one
    simp [lm1]
  | infinite ρ =>
    simp

@[simp]
theorem states_length?_pos : 0 < ef.states.length? := by
  cases ef using indFiniteInfinite <;> simp

def state0 := ef.states[0]'(states_length?_pos _)

section

variable {ef : ts.ExecutionFragment}

theorem isFinite_iff_isFinite : (ef.isFinite = .true) ↔ ((ef.states.isFinite = .true) ∧ (ef.actions.isFinite = .true)) := by
  cases ef using indFiniteInfinite <;> simp

theorem isInfinite_iff_isInfinite : (ef.isInfinite = .true) ↔ ((ef.states.isInfinite = .true) ∧ (ef.actions.isInfinite = .true)) := by
  cases ef using indFiniteInfinite <;> simp

@[simp]
theorem isFinite_imp_states_isFinite (req: ef.isFinite = .true) : ef.states.isFinite = .true := isFinite_iff_isFinite.mp req |>.1

@[simp]
theorem isFinite_imp_actions_isFinite (req: ef.isFinite = .true) : ef.actions.isFinite = .true := isFinite_iff_isFinite.mp req |>.2

@[simp]
theorem isFinite_imp_states_isInfinite (req: ef.isInfinite = .true) : ef.states.isInfinite = .true := isInfinite_iff_isInfinite.mp req |>.1

@[simp]
theorem isFinite_imp_actions_isInfinite (req: ef.isInfinite = .true) : ef.actions.isInfinite = .true := isInfinite_iff_isInfinite.mp req |>.2

end


theorem actions_length?_eq_zero_imp_isFinite (req: ef.actions.length? = 0) : ef.isFinite := by
  cases ef using indFiniteInfinite <;> simp at req
  · dsimp


def refl (state0: ts.S) : ts.ExecutionFragment := ofFinite (.refl state0)

@[defeq, simp]
theorem refl_isFinite {state0} : (@refl ts state0).isFinite = .true := by dsimp [refl]

@[defeq, simp]
theorem refl_actions_length?_eq_zero {state0} : (@refl ts state0).actions.length? = 0 := by
  simp; rfl

@[defeq, simp]
theorem refl_state0 {state0} : (@refl ts state0).state0 = state0 := rfl

theorem refl_eta (req: ef.actions.length? = 0) : (refl ef.state0) = ef := by
  cases ef using indFiniteInfinite with
  | finite ϱ =>
    dsimp [refl]
    congr
    refine FiniteExecutionFragment.refl_eta _ ?_
    simpa using req
  | infinite _ => simp at req

/-
def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ef.state0) : ts.ExecutionFragment :=
  have lm1 := by cases ef using indFiniteInfinite <;> simp
  have lm2 := by
    cases ef using indFiniteInfinite <;> (revert lm1; simp)
    · refine IsExecutionFragment.finite ?_ ?_
      · simp [Sequence.cons_finite]
      · simp [Sequence.cons_finite]
        simp [ExecutionFragment.state0] at req
    --· refine IsExecutionFragment.infinite ?_ ?_
  .mk' (ef.states.cons state0) (ef.actions.cons action0) lm1 lm2
-/



end ExecutionFragment


/-!

### Definition 2.7. Maximal and Initial Execution Fragment

-/

/-
namespace ExecutionFragment

variable {ts: TransitionSystem}

/-- A *maximal* execution fragment is either a finite execution fragment that
ends in a terminal state, or an infinite execution fragment. -/
inductive IsMaximal : ts.ExecutionFragment → Prop where
  | finite (ϱ: ts.FiniteExecutionFragment) (req: ts.IsTerminal ϱ.lastState) : IsMaximal (.finite ϱ)
  | infinite (ρ: ts.InfiniteExecutionFragment) : IsMaximal (.infinite ρ)


def firstState (ef: ts.ExecutionFragment) : ts.S :=
  ExecutionFragment.casesOn ef (fun x => x.firstState) (fun x => x.raw.states 0)

/-- An execution fragment is called initial if it starts in an initial state -/
def IsInitial (ef: ts.ExecutionFragment) : Prop := ef.firstState ∈ ts.I

end ExecutionFragment
-/




end Nemonuri.TransitionSystem

end
