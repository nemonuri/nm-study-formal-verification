module

public import Nemonuri.Executions.ExecutionFragment.Raws
public import Nemonuri.Executions.FiniteExecutionFragment.Basic
public import Nemonuri.Executions.InfiniteExecutionFragment.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem


inductive IsExecutionFragment {ts: TransitionSystem} : ts.ExecutionFragmentRaw → Prop where
  | finite (raw: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment raw) : IsExecutionFragment (.finite raw)
  | infinite (raw: ts.InfiniteExecutionFragmentRaw) (req: ts.IsInfiniteExecutionFragment raw) : IsExecutionFragment (.infinite raw)

namespace IsExecutionFragment

variable {ts: TransitionSystem} {ef: ts.ExecutionFragmentRaw}

theorem to_isFiniteExecutionFragment (h: ts.IsExecutionFragment ef) (req: ef.toLabel = .finite)
  : ts.IsFiniteExecutionFragment (ef.toFinite req) := by
  cases ef <;> cases h
  · simpa
  · simp at req

theorem to_isInfiniteExecutionFragment (h: ts.IsExecutionFragment ef) (req: ef.toLabel = .infinite)
  : ts.IsInfiniteExecutionFragment (ef.toInfinite req) := by
  cases ef <;> cases h
  · simp at req
  · simpa

theorem ofSequence_iff (req: ef.states.toLabel = ef.actions.toLabel)
  : ts.IsExecutionFragment (ExecutionFragmentRaw.ofSequence ef.states ef.actions req) ↔ ts.IsExecutionFragment ef := by
  simp [ExecutionFragmentRaw.ofSequence_eta]

end IsExecutionFragment



structure ExecutionFragment (ts: TransitionSystem) where
  raw: ts.ExecutionFragmentRaw
  is_valid: ts.IsExecutionFragment raw

namespace ExecutionFragment

variable {ts: TransitionSystem} (ef: ts.ExecutionFragment)

def states : Sequence ts.S := ef.raw.states

def actions : Sequence ts.Act := ef.raw.actions

theorem states_toLabel_eq_actions_toLabel : ef.states.toLabel = ef.actions.toLabel := ExecutionFragmentRaw.states_toLabel_eq_actions_toLabel


def mk'
  (states : Sequence ts.S) (actions : Sequence ts.Act)
  (req1: states.toLabel = actions.toLabel)
  (req2: IsExecutionFragment (.ofSequence states actions req1) )
  : ts.ExecutionFragment :=
  ⟨ExecutionFragmentRaw.ofSequence states actions req1, req2⟩


theorem ofSequence_isExecutionFragment : IsExecutionFragment (.ofSequence ef.states ef.actions ef.states_toLabel_eq_actions_toLabel) :=
  (IsExecutionFragment.ofSequence_iff ef.states_toLabel_eq_actions_toLabel).mpr ef.is_valid

theorem mk'_eta
  : (mk' ef.states ef.actions ef.states_toLabel_eq_actions_toLabel ef.ofSequence_isExecutionFragment) = ef := by
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
        (req1: states.toLabel = actions.toLabel) →
        (req2: IsExecutionFragment (.ofSequence states actions req1)) →
        motive (ExecutionFragment.mk' states actions req1 req2))
  (t: ts.ExecutionFragment)
  : motive t :=
  mk' t.states t.actions t.states_toLabel_eq_actions_toLabel t.ofSequence_isExecutionFragment |> Eq.subst t.mk'_eta


def toLabel : Sequence.Label := ef.raw.toLabel


def ofFinite (ϱ: ts.FiniteExecutionFragment) : ts.ExecutionFragment :=
  ⟨.finite ϱ.raw, .finite ϱ.raw ϱ.is_valid⟩

@[defeq, simp]
theorem ofFinite_toLabel {ϱ} : (@ofFinite ts ϱ).toLabel = .finite := by
  dsimp [ofFinite, toLabel]

def toFinite (req: ef.toLabel = .finite) : ts.FiniteExecutionFragment :=
  ⟨ef.raw.toFinite req, (by
    rcases ef with ⟨raw, is_valid⟩
    cases raw
    · dsimp; cases is_valid; assumption
    · simp [toLabel] at req )⟩

@[defeq, simp]
theorem ofFinite_toFinite {ϱ} : (@ofFinite ts ϱ).toFinite ofFinite_toLabel = ϱ := rfl

theorem ofFinite_eta (req: ef.toLabel = .finite) : (ofFinite (ef.toFinite req)) = ef := by
  rcases ef with ⟨raw, is_valid⟩
  cases raw
  · congr
  · simp [toLabel] at req

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
theorem ofInfinite_toLabel {ρ} : (@ofInfinite ts ρ).toLabel = .infinite := by
  dsimp [ofInfinite, toLabel]

def toInfinite (req: ef.toLabel = .infinite) : ts.InfiniteExecutionFragment :=
  ⟨ef.raw.toInfinite req, (by
    rcases ef with ⟨raw, is_valid⟩
    cases raw
    · simp [toLabel] at req
    · dsimp; cases is_valid; assumption )⟩

@[defeq, simp]
theorem ofInfinite_toInfinite {ρ} : (@ofInfinite ts ρ).toInfinite ofInfinite_toLabel = ρ := rfl

theorem ofInfinite_eta (req: ef.toLabel = .infinite) : (ofInfinite (ef.toInfinite req)) = ef := by
  rcases ef with ⟨raw, is_valid⟩
  cases raw
  · simp [toLabel] at req
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
  match lm1: t.toLabel with
  | .finite => finite (t.toFinite lm1) |> Eq.subst (t.ofFinite_eta lm1)
  | .infinite => infinite (t.toInfinite lm1) |> Eq.subst (t.ofInfinite_eta lm1)


@[defeq, simp]
theorem isFinite_indFiniteInfinite (req: ef.toLabel = .finite) {motive finite infinite}
  : @indFiniteInfinite ts motive finite infinite ef = (finite (ef.toFinite req) |> Eq.subst (ef.ofFinite_eta req)) :=
  rfl

@[defeq, simp]
theorem isInfinite_indFiniteInfinite (req: ef.toLabel = .infinite) {motive finite infinite}
  : @indFiniteInfinite ts motive finite infinite ef = (infinite (ef.toInfinite req) |> Eq.subst (ef.ofInfinite_eta req)) :=
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

/-
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
-/

/-
theorem actions_length?_eq_zero_imp_isFinite (req: ef.actions.length? = 0) : ef.isFinite := by
  cases ef using indFiniteInfinite <;> simp at req
  · dsimp
-/


def refl (state0: ts.S) : ts.ExecutionFragment := ofFinite (.refl state0)

@[defeq, simp]
theorem refl_toLabel {state0} : (@refl ts state0).toLabel = .finite := by dsimp [refl]

@[defeq, simp]
theorem refl_actions_eq_nil {state0} : (@refl ts state0).actions = Sequence.nil := rfl

@[defeq, simp]
theorem refl_state0 {state0} : (@refl ts state0).state0 = state0 := rfl

--open scoped EmptyLabel in
theorem refl_eta (req: ef.actions.toEmptyLabel = .empty) : (refl ef.state0) = ef := by
  cases ef using indFiniteInfinite with
  | finite ϱ =>
    dsimp [refl]
    congr
    refine FiniteExecutionFragment.refl_eta _ ?_
    simp [EmptyLabel.ofNat_empty_iff_eq_zero] at req
    simpa using req
  | infinite _ => simp at req


def toExecutionLabel := ef.raw.toExecutionLabel

theorem tail_preserves_states_isFinite_eq_actions_isFinite
  : ef.states.tail.isFinite = ef.actions.tail.isFinite := by
  simp [Sequence.tail_isFinite]
  exact ef.states_isFinite_eq_actions_isFinite

theorem tail_preserves_isExecutionFragment (req: 0 < ef.actions.length?)
  : IsExecutionFragment (.ofSequence ef.states.tail ef.actions.tail ef.raw.tail.states_toLabel_eq_actions_toLabel) := by
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
