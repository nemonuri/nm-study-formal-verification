module

public import Nemonuri.Executions.ExecutionFragment.Raw
public import Nemonuri.Executions.FiniteExecutionFragment.Basic
public import Nemonuri.Executions.InfiniteExecutionFragment.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem


inductive IsExecutionFragment {ts: TransitionSystem} : ts.ExecutionFragmentRaw → Prop where
  | finite (raw: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment raw) : IsExecutionFragment (.finite raw)
  | infinite (raw: ts.InfiniteExecutionFragmentRaw) (req: ts.IsInfiniteExecutionFragment raw) : IsExecutionFragment (.infinite raw)

namespace IsExecutionFragment

variable {ts: TransitionSystem} {ef: ts.ExecutionFragmentRaw}

theorem to_isFiniteExecutionFragment (h: ts.IsExecutionFragment ef) (req: ef.toLabel = .finite) :


end IsExecutionFragment



structure ExecutionFragment (ts: TransitionSystem) where
  raw: ts.ExecutionFragmentRaw
  is_valid: ts.IsExecutionFragment raw

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
  ⟨.finite ϱ.raw, .finite ϱ.raw ϱ.is_valid⟩

@[defeq, simp]
theorem ofFinite_isFinite {ϱ} : (@ofFinite ts ϱ).isFinite = .true := by
  dsimp [ofFinite, isFinite]

@[defeq]
theorem ofFinite_isInfinite {ϱ} : (@ofFinite ts ϱ).isInfinite = .false := by
  apply Bool.not_inj; simp


def getFinite (req: ef.isFinite) : ts.FiniteExecutionFragment :=
  ⟨ef.raw.getFinite req, (by
    rcases ef with ⟨raw, is_valid⟩
    cases raw
    · dsimp; cases is_valid; assumption
    · simp [ExecutionFragment.isFinite] at req )⟩

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

@[defeq]
theorem ofFinite_eq_mk' {ϱ}
  : Eq (@ofFinite ts ϱ)
       (ExecutionFragment.mk' (.finite ϱ.states) (.finite ϱ.actions) rfl (.finite ϱ.raw ϱ.is_valid))
  := rfl



def ofInfinite (ρ: ts.InfiniteExecutionFragment) : ts.ExecutionFragment :=
  ⟨.infinite ρ.raw, .infinite ρ.raw ρ.is_valid⟩

@[defeq, simp]
theorem ofInfinite_isInfinite {ρ} : (@ofInfinite ts ρ).isInfinite = .true := by
  dsimp [ofInfinite, isInfinite]

@[defeq]
theorem ofInfinite_isFinite {ρ} : (@ofInfinite ts ρ).isFinite = .false := by
  apply Bool.not_inj; simp

def getInfinite (req: ef.isInfinite) : ts.InfiniteExecutionFragment :=
  ⟨ef.raw.getInfinite req, (by
    rcases ef with ⟨raw, is_valid⟩
    cases raw
    · simp [ExecutionFragment.isInfinite] at req
    · dsimp; cases is_valid; assumption
    )⟩

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

@[defeq]
theorem ofInfinite_eq_mk' {ρ}
  : Eq (@ofInfinite ts ρ)
       (ExecutionFragment.mk' (.infinite ρ.states) (.infinite ρ.actions) rfl (.infinite ρ.raw ρ.is_valid))
  := rfl


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


@[defeq, simp]
theorem ofFinite_state0 {ϱ} : (@ofFinite ts ϱ).state0 = ϱ.state0 := rfl

@[defeq, simp]
theorem ofInfinite_state0 {ρ} : (@ofInfinite ts ρ).state0 = ρ.state0 := rfl




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


theorem tail_preserves_states_isFinite_eq_actions_isFinite
  : ef.states.tail.isFinite = ef.actions.tail.isFinite := by
  simp [Sequence.tail_isFinite]
  exact ef.states_isFinite_eq_actions_isFinite

theorem tail_preserves_isExecutionFragment (req: 0 < ef.actions.length?)
  : IsExecutionFragment (.ofSequence ef.states.tail ef.actions.tail ef.tail_preserves_states_isFinite_eq_actions_isFinite) := by
  cases ef using indFiniteInfinite
  · refine IsExecutionFragment.finite _ ?_
    refine FiniteExecutionFragment.tail_preserves_isFiniteExecutionFragment _ ?_
    simpa using req
  · refine IsExecutionFragment.infinite _ ?_
    refine InfiniteExecutionFragment.tail_preserves_isInfiniteExecutionFragment _


theorem ofFinite_actions_length_pos_iff {ϱ}
  : (0 < (@ofFinite ts ϱ).actions.length?) ↔ (0 < ϱ.actions.length) := by
  simp

theorem ofInfinite_actions_length_pos {ρ}
  : 0 < (@ofInfinite ts ρ).actions.length? := by
  simp


def tail (req: 0 < ef.actions.length?) : ts.ExecutionFragment :=
  .mk' (ef.states.tail) (ef.actions.tail)
    (ef.tail_preserves_states_isFinite_eq_actions_isFinite) (ef.tail_preserves_isExecutionFragment req)

@[defeq, simp]
theorem ofFinite_tail {ϱ req} : ((@ofFinite ts ϱ).tail req) = (@ofFinite ts (ϱ.tail (ofFinite_actions_length_pos_iff.mp req))) := by
  dsimp [tail, Sequence.tail_finite]; rfl

@[defeq, simp]
theorem ofInfinite_tail {ρ} : (@ofInfinite ts ρ).tail ofInfinite_actions_length_pos = (@ofInfinite ts ρ.tail) := by
  dsimp [tail, Sequence.tail_infinite]; rfl


def action0 (req: 0 < ef.actions.length?) : ts.Act := ef.actions[0]'(req)





theorem stepL_preserves_states_isFinite_eq_actions_isFinite
  {state0: ts.S} {action0: ts.Act}
  : (ef.states.cons state0).isFinite = (ef.actions.cons action0).isFinite := by
  simp only [Sequence.cons_isFinite]
  exact ef.states_isFinite_eq_actions_isFinite

theorem stepL_preserves_isExecutionFragment
  {state0: ts.S} {action0: ts.Act} (req: state0 ─⌞action0⌟→{ts} ef.state0)
  : IsExecutionFragment (.ofSequence (ef.states.cons state0) (ef.actions.cons action0) ef.stepL_preserves_states_isFinite_eq_actions_isFinite) := by
    cases ef using indFiniteInfinite --with
    · refine IsExecutionFragment.finite _ ?_
      refine FiniteExecutionFragment.stepL_preserves_isFiniteExecutionFragment _ ?_
      simpa using req
    · refine IsExecutionFragment.infinite _ ?_
      refine InfiniteExecutionFragment.stepL_preserves_isInfiniteExecutionFragment _ ?_
      simpa using req


def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ef.state0) : ts.ExecutionFragment :=
  .mk' (ef.states.cons state0) (ef.actions.cons action0)
    (ef.stepL_preserves_states_isFinite_eq_actions_isFinite) (ef.stepL_preserves_isExecutionFragment req)

@[simp]
theorem stepL_actions_length?_pos {state0 action0 req}
  : 0 < (ef.stepL state0 action0 req).actions.length? := by
  simp [stepL]

theorem tail_canStepL (req: 0 < ef.actions.length?)
  : ef.state0 ─⌞(ef.action0 req)⌟→{ts} (ef.tail req).state0 := by
  cases ef using indFiniteInfinite with
  | finite ϱ =>
    refine ϱ.state0_action0_tail_state0 ?_
  | infinite ρ =>
    refine ρ.tail_canStepL


open Cslib in
theorem stepL_eta (req: 0 < ef.actions.length?)
  : (stepL (ef.tail req) (ef.state0) (ef.action0 req) (ef.tail_canStepL req)) = ef := by
  cases ef using indFiniteInfinite
  · revert req; simp; intro req
    dsimp [stepL]
    simp [Sequence.cons_finite]
    conv => rhs; rw [ofFinite_eq_mk']
    congr
    · dsimp [FiniteExecutionFragment.state0]
      simp [List.getElem_zero_eq_head]
    · dsimp [ExecutionFragment.action0]
      simp [Sequence.getElem_eq_list, List.getElem_zero_eq_head]
  · dsimp [stepL]
    simp [Sequence.cons_infinite]
    conv => rhs; rw [ofInfinite_eq_mk']
    congr
    · dsimp [InfiniteExecutionFragment.state0]
      simp only [ωSequence.eta]
    · dsimp [ExecutionFragment.action0]
      refine Eq.subst ?_ (ωSequence.eta _)
      rfl

@[elab_as_elim]
def indReflStepL
  {motive: ts.ExecutionFragment → Sort _}
  (refl: (state0: ts.S) → motive (ExecutionFragment.refl state0))
  (stepL: (tail: ts.ExecutionFragment) → (state0: ts.S) → (action0: ts.Act) →
          (req: state0 ─⌞action0⌟→{ts} tail.state0) →
          motive (ExecutionFragment.stepL tail state0 action0 req))
  (t: ts.ExecutionFragment)
  : motive t :=
  if lm1: t.actions.length? = 0 then
    refl t.state0 |> Eq.subst (t.refl_eta lm1)
  else
    have lm2 := Sequence.length?_ne_zero_iff_pos.mp lm1
    stepL (t.tail lm2) (t.state0) (t.action0 lm2) (t.tail_canStepL lm2) |> Eq.subst (t.stepL_eta lm2)



end ExecutionFragment

end Nemonuri.TransitionSystem

end
