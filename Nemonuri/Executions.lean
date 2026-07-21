module

public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Nemonuri.TransitionSystem

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



namespace FiniteExecutionFragment

variable {ts: TransitionSystem} (ϱ: ts.FiniteExecutionFragment)

protected def states := ϱ.raw.states

protected def actions := ϱ.raw.actions

theorem states_length_pos : 0 < ϱ.states.length :=
  calc ϱ.states.length
    _ = _ := by dsimp only [FiniteExecutionFragment.states]
    _ = _ := ϱ.is_valid.length_eq
    _ > 0 := by
      dsimp only [GT.gt]
      exact Nat.add_one_pos _

theorem states_ne_nil : ϱ.states ≠ [] := List.length_pos_iff.mp ϱ.states_length_pos


def firstState : ts.S := ϱ.states[0]'(ϱ.states_length_pos)


theorem states_length_sub_one_lt_self : ϱ.states.length - 1 < ϱ.states.length := Nat.sub_succ_lt_self _ 0 ϱ.states_length_pos

def lastState : ts.S := ϱ.states[ϱ.states.length - 1]'(ϱ.states_length_sub_one_lt_self)


open Cslib.LTS in
theorem isFiniteExecutionFragment_iff_execution
  : ts.IsFiniteExecutionFragment ϱ.raw ↔ ts.lts.Execution ϱ.firstState ϱ.actions ϱ.lastState ϱ.states := by
  dsimp only [Execution]
  constructor
  · rintro ⟨length_eq, states_actions_valid⟩
    exists length_eq
  · rintro ⟨length_eq, _, _, states_actions_valid⟩
    exact IsFiniteExecutionFragment.mk length_eq states_actions_valid


theorem firstState_eq_head : ϱ.firstState = ϱ.states.head ϱ.states_ne_nil := by
  dsimp only [FiniteExecutionFragment.firstState]
  rw [List.head_eq_getElem]


theorem lastState_eq_getLast : ϱ.lastState = ϱ.states.getLast ϱ.states_ne_nil := by
  dsimp only [FiniteExecutionFragment.lastState]
  rw [List.getLast_eq_getElem]

def length : Nat := ϱ.actions.length

@[defeq] theorem length_eq_actions_length : ϱ.length = ϱ.actions.length := rfl

theorem length_add_one_eq_states_length : ϱ.length + 1 = ϱ.states.length := by
  dsimp [length_eq_actions_length, FiniteExecutionFragment.states, FiniteExecutionFragment.actions]
  rw [ϱ.is_valid.length_eq]



protected def refl (ts: TransitionSystem) (s: ts.S) : FiniteExecutionFragment ts where
  raw := .mk [s] []
  is_valid := by constructor <;> simp

theorem length_eq_zero_iff_actions_eq_nil : (ϱ.length = 0) ↔ (ϱ.actions = []) :=
  calc
    _ ↔ _ := by dsimp only [ϱ.length_eq_actions_length]; rfl
    _ ↔ _ := by simp only [List.length_eq_zero_iff]



theorem length_eq_zero_iff_states_eq_singleton : (ϱ.length = 0) ↔ (ϱ.states = [ϱ.firstState]) := by
  refine Iff.trans (Nat.add_one_inj.symm) ?_
  rw [ϱ.length_add_one_eq_states_length]
  dsimp [FiniteExecutionFragment.firstState]
  refine Iff.trans (List.length_eq_one_iff) ?_
  constructor
  · rintro ⟨s, lm1⟩; simp only [lm1, List.getElem_cons_zero]
  · intro lm1; exact Exists.intro _ lm1

theorem length_eq_zero_imp_firstState_eq_lastState (h: ϱ.length = 0)
  : ϱ.firstState = ϱ.lastState := by
  dsimp [FiniteExecutionFragment.firstState, FiniteExecutionFragment.lastState]
  simp [← ϱ.length_add_one_eq_states_length, h]


theorem length_eq_zero_iff_refl_eq : (ϱ.length = 0) ↔ (∃s, ϱ = FiniteExecutionFragment.refl ts s) := by
  dsimp only [FiniteExecutionFragment.refl]
  constructor
  · intro lm1
    have lm2 := ϱ.length_eq_zero_iff_actions_eq_nil.mp lm1
    have lm3 := ϱ.length_eq_zero_iff_states_eq_singleton.mp lm1
    exists ϱ.firstState
    conv =>
      rhs; arg 1
      conv => arg 1; rw [← lm3]
      conv => arg 2; rw [← lm2]
    rfl
  · rintro ⟨s, lm1⟩
    rw [ϱ.length_eq_zero_iff_actions_eq_nil]
    subst lm1
    dsimp only [FiniteExecutionFragment.actions]


protected def stepL (s: ts.S) (act: ts.Act) (req: s ─⌞act⌟→{ts} ϱ.firstState) : FiniteExecutionFragment ts where
  raw := .mk (s :: ϱ.states) (act :: ϱ.actions)
  is_valid := by
    constructor
    · dsimp
      intro i lm1
      induction i with
      | zero =>
        dsimp
        simpa only [FiniteExecutionFragment.firstState] using req
      | succ i _ =>
        dsimp
        refine ϱ.is_valid.states_actions_valid i ?_
    · dsimp
      rw [← ϱ.length_add_one_eq_states_length, ϱ.length_eq_actions_length]


theorem stepL_length_pos {ϱ: ts.FiniteExecutionFragment} {s act req}
  : 0 < (ϱ.stepL s act req).length := by
  dsimp [FiniteExecutionFragment.stepL, length_eq_actions_length, FiniteExecutionFragment.actions]
  exact Nat.add_one_pos _


structure StepLEntry (ts : TransitionSystem) where
  ϱ: ts.FiniteExecutionFragment
  s: ts.S
  act: ts.Act
  req: s ─⌞act⌟→{ts} ϱ.firstState

protected def StepLEntry.stepL (sle: StepLEntry ts) : FiniteExecutionFragment ts :=
  sle.ϱ.stepL sle.s sle.act sle.req


def stepLInv (ϱ': ts.FiniteExecutionFragment) (req: 0 < ϱ'.length) : StepLEntry ts where
  ϱ := {
    raw := {
      states := ϱ'.states.tail
      actions := ϱ'.actions.tail
    }
    is_valid := by
      constructor
      · simp only [List.length_tail, List.getElem_tail]
        intro i lm1
        refine ϱ'.is_valid.states_actions_valid (i+1) ?_
      · simp only [List.length_tail]
        rw [← ϱ'.length_add_one_eq_states_length, ← ϱ'.length_eq_actions_length]
        omega
  }
  s := ϱ'.firstState
  act := ϱ'.actions.head (List.length_pos_iff.mp req)
  req := by
    dsimp [FiniteExecutionFragment.firstState]
    rw [List.head_eq_getElem]
    conv =>
      arg 4; dsimp [FiniteExecutionFragment.states]; simp only [List.getElem_tail]
    refine ϱ'.is_valid.states_actions_valid 0 ?_


theorem stepInv_stepL_leftInverse (h: 0 < ϱ.length) : (ϱ.stepLInv h).stepL = ϱ := by
  dsimp [
    StepLEntry.stepL, FiniteExecutionFragment.stepL, FiniteExecutionFragment.stepLInv,
    FiniteExecutionFragment.states, FiniteExecutionFragment.actions
  ]
  simp only [firstState_eq_head, FiniteExecutionFragment.states, List.cons_head_tail]


theorem length_pos_iff_stepL_eq
  : (0 < ϱ.length) ↔ (∃(sle: StepLEntry ts), ϱ = sle.stepL) := by
  constructor
  · intro lm1
    exists (ϱ.stepLInv lm1)
    rw [ϱ.stepInv_stepL_leftInverse]
  · rintro ⟨sle, lm1⟩
    subst lm1
    dsimp [StepLEntry.stepL]
    exact stepL_length_pos


@[elab_as_elim, induction_eliminator]
protected def ind
  {motive : ts.FiniteExecutionFragment → Sort _}
  (refl: (s: ts.S) → motive <| FiniteExecutionFragment.refl ts s )
  (stepL: (ϱ : ts.FiniteExecutionFragment) → (s: ts.S) → (act: ts.Act) → (req: s ─⌞act⌟→{ts} ϱ.firstState) → motive <| ϱ.stepL s act req)
  (t: ts.FiniteExecutionFragment)
  : motive t :=
  if h1: t.length = 0 then
    refl t.firstState |> cast (by
      congr
      obtain ⟨s, lm1⟩ := t.length_eq_zero_iff_refl_eq.mp h1
      subst lm1
      rfl )
  else
    let sle : StepLEntry ts := t.stepLInv (Nat.ne_zero_iff_zero_lt.mp h1)
    stepL sle.ϱ sle.s sle.act sle.req |> cast (by
      congr
      subst sle
      obtain ⟨sle, lm1⟩ := t.length_pos_iff_stepL_eq.mp (Nat.ne_zero_iff_zero_lt.mp h1)
      subst lm1
      rfl )

@[elab_as_elim, cases_eliminator]
protected def indOn
  {motive : ts.FiniteExecutionFragment → Sort _}
  (t: ts.FiniteExecutionFragment)
  (refl: (s: ts.S) → motive <| FiniteExecutionFragment.refl ts s )
  (stepL: (ϱ : ts.FiniteExecutionFragment) → (s: ts.S) → (act: ts.Act) → (req: s ─⌞act⌟→{ts} ϱ.firstState) → motive <| ϱ.stepL s act req)
  : motive t :=
  @FiniteExecutionFragment.ind ts motive refl stepL t

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

/-

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

/-- The term `execution fragment` will be used to denote either a finite or an infinite execution fragment -/
inductive ExecutionFragment (ts: TransitionSystem) where
  | finite (ϱ: ts.FiniteExecutionFragment) : ExecutionFragment ts
  | infinite (ρ: ts.InfiniteExecutionFragment) : ExecutionFragment ts

end Definition

/-!

### Definition 2.7. Maximal and Initial Execution Fragment

-/

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
