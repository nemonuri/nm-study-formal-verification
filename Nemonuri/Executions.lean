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

def length : Nat := pf.actions.length

@[defeq]
theorem length_eq_actions_length : pf.length = pf.actions.length := rfl

theorem length_eq_states_length : pf.length = pf.states.length := by
  dsimp [length_eq_actions_length, ExecutionFragmentPrefix.actions, ExecutionFragmentPrefix.states]
  exact pf.is_valid.length_eq.symm


protected def nil (ts: TransitionSystem) : ts.ExecutionFragmentPrefix where
  raw := .mk [] []
  is_valid := by
    constructor
    · simp
    · simp

theorem length_eq_zero_iff_nil : (pf.length = 0) ↔ (pf = ExecutionFragmentPrefix.nil ts) := by
  constructor
  · intro lm1
    have lm2 := pf.length_eq_actions_length.symm.trans lm1 |> List.length_eq_zero_iff.mp
    have lm3 := pf.length_eq_states_length.symm.trans lm1  |> List.length_eq_zero_iff.mp
    dsimp [ExecutionFragmentPrefix.nil]
    conv =>
      rhs; arg 1
      conv => rw [← lm3]
      conv => rw [← lm2]
    rfl
  · intro lm1; subst lm1
    dsimp [ExecutionFragmentPrefix.nil, ExecutionFragmentPrefix.length, ExecutionFragmentPrefix.actions]


def firstState (req: 0 < pf.length) : ts.S := pf.states[0]'(pf.length_eq_states_length ▸ req)

protected def stepL
  (s: ts.S) (act: ts.Act)
  (req: (h: 0 < pf.length) → (s ─⌞act⌟→{ts} (pf.firstState h))) : ts.ExecutionFragmentPrefix where
  raw := .mk (s :: pf.states) (act :: pf.actions)
  is_valid := by
    constructor
    · dsimp
      intro i lm1
      induction i with
      | zero =>
        dsimp
        dsimp [firstState] at req
        exact req lm1
      | succ i _ =>
        dsimp [ExecutionFragmentPrefix.states, ExecutionFragmentPrefix.actions] at lm1 ⊢
        refine pf.is_valid.states_actions_valid i ?_
        exact Nat.lt_sub_of_add_lt lm1
    · dsimp; rw [← pf.length_eq_actions_length, ← pf.length_eq_states_length]

theorem stepL_length_pos {pf : ts.ExecutionFragmentPrefix} {s act req}
  : 0 < (pf.stepL s act req).length := by
  dsimp [ExecutionFragmentPrefix.length, ExecutionFragmentPrefix.actions, ExecutionFragmentPrefix.stepL]
  exact Nat.add_one_pos _

structure StepLEntry (ts : TransitionSystem) where
  pf: ts.ExecutionFragmentPrefix
  s: ts.S
  act: ts.Act
  req (h: 0 < pf.length) : s ─⌞act⌟→{ts} (pf.firstState h)

def StepLEntry.stepL (sle: StepLEntry ts) : ts.ExecutionFragmentPrefix :=
  sle.pf.stepL sle.s sle.act sle.req

def stepLInv (pf': ts.ExecutionFragmentPrefix) (req: 0 < pf'.length) : StepLEntry ts where
  pf := {
    raw := {
      states := pf'.states.tail
      actions := pf'.actions.tail
    }
    is_valid := by
      constructor
      · simp
        intro i lm1
        refine pf'.is_valid.states_actions_valid (i+1) ?_
        dsimp [ExecutionFragmentPrefix.length_eq_actions_length, ExecutionFragmentPrefix.actions] at req lm1
        omega
      · simp only [List.length_tail]
        rw [← pf'.length_eq_actions_length, ← pf'.length_eq_states_length]
  }
  s := pf'.firstState req
  act := pf'.actions[0]'(pf'.length_eq_actions_length ▸ req)
  req := by
    dsimp
    intro lm1
    dsimp [ExecutionFragmentPrefix.firstState]
    conv => arg 4; dsimp [ExecutionFragmentPrefix.states]; simp
    refine pf'.is_valid.states_actions_valid 0 ?_
    dsimp [ExecutionFragmentPrefix.length_eq_actions_length, ExecutionFragmentPrefix.actions] at lm1
    simpa using lm1


theorem stepInv_stepL_leftInverse (req: 0 < pf.length)
  : (pf.stepLInv req).stepL = pf := by
  dsimp [
      ExecutionFragmentPrefix.StepLEntry.stepL, ExecutionFragmentPrefix.stepL, ExecutionFragmentPrefix.stepLInv,
      ExecutionFragmentPrefix.firstState, ExecutionFragmentPrefix.states, ExecutionFragmentPrefix.actions
    ]
  have lm1 := pf.length_eq_states_length ▸ req
  have lm2 := pf.length_eq_actions_length ▸ req
  have lm3 := List.head_eq_getElem (List.length_pos_iff.mp lm1)
  dsimp [ExecutionFragmentPrefix.states] at lm3
  simp only [← lm3]
  have lm4 := List.head_eq_getElem (List.length_pos_iff.mp lm2)
  dsimp [ExecutionFragmentPrefix.actions] at lm4
  simp only [← lm4]
  simp only [List.cons_head_tail]



theorem length_pos_iff_stepL_eq : (0 < pf.length) ↔ (∃(sle: StepLEntry ts), pf = sle.stepL) := by
  constructor
  · intro lm1
    exists (pf.stepLInv lm1)
    exact (pf.stepInv_stepL_leftInverse lm1).symm
  · rintro ⟨sle, lm1⟩
    subst lm1
    dsimp [ExecutionFragmentPrefix.StepLEntry.stepL]
    exact stepL_length_pos



@[elab_as_elim, induction_eliminator]
protected def ind
  {motive : ts.ExecutionFragmentPrefix → Sort _}
  (nil: motive <| ExecutionFragmentPrefix.nil ts )
  (stepL:
    (pf: ts.ExecutionFragmentPrefix) → (s: ts.S) →
    (act: ts.Act) → (req: (h: 0 < pf.length) → s ─⌞act⌟→{ts} (pf.firstState h)) →
    motive <| ExecutionFragmentPrefix.stepL pf s act req )
  (t: ts.ExecutionFragmentPrefix)
  : motive t :=
  if h1: t.length = 0 then
    nil |> cast (by
      congr
      have lm1 := t.length_eq_zero_iff_nil.mp h1
      exact lm1.symm
    )
  else
    let sle : StepLEntry ts := t.stepLInv (Nat.pos_iff_ne_zero.mpr h1)
    stepL sle.pf sle.s sle.act sle.req |> cast (by
      congr
      subst sle
      exact t.stepInv_stepL_leftInverse _
    )


@[elab_as_elim, cases_eliminator]
protected def indOn
  {motive : ts.ExecutionFragmentPrefix → Sort _}
  (t: ts.ExecutionFragmentPrefix)
  (nil: motive <| ExecutionFragmentPrefix.nil ts )
  (stepL:
    (pf: ts.ExecutionFragmentPrefix) → (s: ts.S) →
    (act: ts.Act) → (req: (h: 0 < pf.length) → s ─⌞act⌟→{ts} (pf.firstState h)) →
    motive <| ExecutionFragmentPrefix.stepL pf s act req )
  : motive t :=
  @ExecutionFragmentPrefix.ind ts motive nil stepL t


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


section Definition

open Cslib

variable {ts: TransitionSystem}

structure InfiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states : ωSequence ts.S
  actions : ωSequence ts.Act

structure IsInfiniteExecutionFragment (raw: ts.InfiniteExecutionFragmentRaw) : Prop where
  ofPred :: toPred : ((i: Nat) → (raw.states i) ─⌞(raw.actions i)⌟→{ts} (raw.states (i + 1)))


theorem isInfiniteExecutionFragment_iff_omegaExecution (raw: ts.InfiniteExecutionFragmentRaw)
  : ts.IsInfiniteExecutionFragment raw ↔ ts.lts.OmegaExecution raw.states raw.actions := by
  constructor
  · rintro ⟨toPred⟩; exact toPred
  · intro lm1; exact .ofPred lm1


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



inductive ExecutionFragmentRaw (ts: TransitionSystem) where
  | finite (ϱ: ts.FiniteExecutionFragmentRaw)
  | infinite (ρ: ts.InfiniteExecutionFragmentRaw)

namespace ExecutionFragmentRaw

variable {ts: TransitionSystem} {raw: ts.ExecutionFragmentRaw}


def states : ts.ExecutionFragmentRaw → Sequence ts.S
  | .finite ϱ => .finite ϱ.states
  | .infinite ρ => .infinite ρ.states

@[simp]
theorem finite_states {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).states = (.finite ϱ.states) := rfl

@[simp]
theorem infinite_states {ρ} : (@ExecutionFragmentRaw.infinite ts ρ).states = (.infinite ρ.states) := rfl


def actions : ts.ExecutionFragmentRaw → Sequence ts.Act
  | .finite ϱ => .finite ϱ.actions
  | .infinite ρ => .infinite ρ.actions

@[simp]
theorem finite_actions {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).actions = (.finite ϱ.actions) := rfl

@[simp]
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
theorem ofSequence_states_eq {states: Sequence ts.S} {actions req}
  : (ofSequence states actions req).states = states := by
  dsimp [ofSequence]
  cases states <;> cases actions <;> simp at req <;> simp

@[simp]
theorem ofSequence_actions_eq {states: Sequence ts.S} {actions req}
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



def isInfinite : ts.ExecutionFragmentRaw → Bool
  | .finite _ => .false
  | .infinite _ => .true

@[simp, grind =]
theorem isInfinite_finite {ϱ: ts.FiniteExecutionFragmentRaw} : isInfinite (.finite ϱ) = .false := rfl

@[simp, grind =]
theorem isInfinite_infinite {ρ: ts.InfiniteExecutionFragmentRaw} : isInfinite (.infinite ρ) = .true := rfl


@[simp, grind =]
theorem not_isFinite_eq_isInfinite
  : (!raw.isFinite) = raw.isInfinite := by
  cases raw <;> simp

@[simp, grind =]
theorem not_isInfinite_eq_isFinite
  : (!raw.isInfinite) = raw.isFinite := by
  cases raw <;> simp

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

end ExecutionFragmentRaw





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
