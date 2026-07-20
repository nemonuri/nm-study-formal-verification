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


end FiniteExecutionFragment


/-


protected def refl (ts: TransitionSystem) (s: ts.S) : FiniteExecutionFragment ts where
  raw := .mk s [] s [s]
  is_valid := by constructor <;> simp


theorem length_eq_zero_iff_actions_eq_nil : (ϱ.length = 0) ↔ (ϱ.raw.actions = []) :=
  calc
    _ ↔ _ := by dsimp only [FiniteExecutionFragment.length]; rfl
    _ ↔ _ := by simp only [List.length_eq_zero_iff]


theorem length_eq_zero_iff_states_eq_singleton : (ϱ.length = 0) ↔ (ϱ.raw.states = [ϱ.firstState]) :=
  calc (ϱ.length = 0)
    _ ↔ _ := by dsimp only [FiniteExecutionFragment.length]; rfl
    _ ↔ ϱ.raw.states.length = 1 := by simp [ϱ.is_valid.length_eq]
    _ ↔ _ := List.length_eq_one_iff
    _ ↔ _ := by
      constructor
      · rintro ⟨s, lm1⟩
        cases lm2: ϱ.raw.states with
        | nil => rewrite [lm2] at lm1; simp at lm1
        | cons hd tl =>
          simp only [ϱ.firstState_eq_head]
          simp [lm2]
          simp [lm1] at lm2
          exact lm2.right
      · intro lm1
        exact Exists.intro _ lm1


theorem length_eq_zero_imp_firstState_eq_lastState (h: ϱ.length = 0)
  : ϱ.firstState = ϱ.lastState := by
  have lm1 := ϱ.length_eq_zero_iff_states_eq_singleton.mp h
  simp only [FiniteExecutionFragment.firstState_eq_head, FiniteExecutionFragment.lastState_eq_getLast]
  simp [lm1]


theorem length_eq_zero_iff_refl_eq : (ϱ.length = 0) ↔ (∃s, ϱ = FiniteExecutionFragment.refl ts s) := by
  constructor
  · intro lm1
    have lm2 := ϱ.length_eq_zero_iff_actions_eq_nil.mp lm1
    have lm3 := ϱ.length_eq_zero_iff_states_eq_singleton.mp lm1
    have lm4 := ϱ.length_eq_zero_imp_firstState_eq_lastState lm1
    exists ϱ.firstState
    dsimp [FiniteExecutionFragment.refl]
    conv =>
      rhs; arg 1
      conv => arg 1; dsimp only [FiniteExecutionFragment.firstState]
      conv => arg 2; rw [← lm2]
      conv => arg 3; rw [lm4]; dsimp only [FiniteExecutionFragment.lastState]
      conv => arg 4; rw [← lm3]
  · rintro ⟨s, lm1⟩
    subst lm1
    dsimp [FiniteExecutionFragment.refl, FiniteExecutionFragment.length]




protected def stepL (s: ts.S) (act: ts.Act) (req: s ─⌞act⌟→{ts} ϱ.firstState) : FiniteExecutionFragment ts where
  raw := .mk s (act :: ϱ.raw.actions) ϱ.lastState (s :: ϱ.raw.states)
  is_valid := by
    constructor
    · dsimp
    · simp [lastState_eq_getElem, ϱ.is_valid.length_eq]
    · dsimp
      intro i lm1
      induction i with
      | zero =>
        dsimp
        simpa only [firstState_eq_getElem] using req
      | succ i _ =>
        dsimp
        refine ϱ.is_valid.states_actions_valid i ?_
    · dsimp
      simp [ϱ.is_valid.length_eq]

theorem stepL_length_pos {ϱ: ts.FiniteExecutionFragment} {s act req}
  : 0 < (ϱ.stepL s act req).length := by
  dsimp [FiniteExecutionFragment.stepL, length_eq_actions_length]
  simp


structure StepLEntry (ts : TransitionSystem) where
  ϱ: ts.FiniteExecutionFragment
  s: ts.S
  act: ts.Act
  req: s ─⌞act⌟→{ts} ϱ.firstState

protected def StepLEntry.stepL (sle: StepLEntry ts) : FiniteExecutionFragment ts :=
  sle.ϱ.stepL sle.s sle.act sle.req


protected def stepLInv (ϱ': ts.FiniteExecutionFragment) (req: 0 < ϱ'.length) : StepLEntry ts :=
  have lm1 := ϱ'.length_eq_actions_length ▸ req
  have lm2 : 1 < ϱ'.raw.states.length := by have _ := ϱ'.length_eq_states_length_sub_one ▸ req; omega
  {
    ϱ := {
      raw := {
        firstState := ϱ'.raw.states[1]'(lm2)
        actions := ϱ'.raw.actions.tail
        lastState := ϱ'.lastState
        states := ϱ'.raw.states.tail
      }
      is_valid := by
        constructor
        · dsimp; simp only [List.getElem_tail, zero_add]
        · dsimp
          simp [lastState_eq_getElem]
          congr
          omega
        · dsimp; simp only [List.length_tail, List.getElem_tail]
          intro i lm3
          refine ϱ'.is_valid.states_actions_valid (i+1) ?_
        · dsimp; simp only [List.length_tail]
          rw [ϱ'.is_valid.length_eq]
          omega
    }
    s := ϱ'.firstState
    act := ϱ'.raw.actions.head (List.length_pos_iff.mp req)
    req := by
      dsimp [FiniteExecutionFragment.firstState]
      rw [← ϱ'.is_valid.firstState_eq]
      rw [List.head_eq_getElem]
      exact ϱ'.is_valid.states_actions_valid 0 lm1
  }



theorem stepInv_stepL_leftInverse (h: 0 < ϱ.length) : (ϱ.stepLInv h).stepL = ϱ := by
  dsimp [StepLEntry.stepL, FiniteExecutionFragment.stepL, FiniteExecutionFragment.stepLInv]
  simp only [List.cons_head_tail]
  dsimp [FiniteExecutionFragment.firstState, FiniteExecutionFragment.lastState]
  conv =>
    lhs; arg 1; arg 4;
    simp only [← FiniteExecutionFragment.firstState.eq_1]
    simp [FiniteExecutionFragment.firstState_eq_head]



theorem length_pos_iff_stepL_eq
  : (0 < ϱ.length) ↔ (∃(sle: StepLEntry ts), ϱ = sle.stepL) := by
  constructor
  · intro lm1
    exists (ϱ.stepLInv lm1)
    rw [stepInv_stepL_leftInverse]
  · rintro ⟨sle, lm1⟩
    subst lm1
    dsimp [StepLEntry.stepL]
    simp only [stepL_length_pos]

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
