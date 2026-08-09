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

theorem to_isFiniteExecutionFragment (h: ts.IsExecutionFragment ef) (req: ef.toSeqLabel = .finite)
  : ts.IsFiniteExecutionFragment (ef.toFinite req) := by
  cases ef <;> cases h
  · simpa
  · simp at req

theorem to_isInfiniteExecutionFragment (h: ts.IsExecutionFragment ef) (req: ef.toSeqLabel = .infinite)
  : ts.IsInfiniteExecutionFragment (ef.toInfinite req) := by
  cases ef <;> cases h
  · simp at req
  · simpa

theorem ofSequence_eta_congr --(req: ef.states.toLabel = ef.actions.toLabel)
  : ts.IsExecutionFragment (.ofSequence ef.states ef.actions ef.states_toLabel_eq_actions_toLabel) ↔ ts.IsExecutionFragment ef := by
  simp [ExecutionFragmentRaw.ofSequence_eta]

theorem to_ofSequence_eta (h: ts.IsExecutionFragment ef)
  : ts.IsExecutionFragment (.ofSequence ef.states ef.actions ef.states_toLabel_eq_actions_toLabel) :=
  ofSequence_eta_congr.mpr h

theorem states_nonempty (h: ts.IsExecutionFragment ef) : ef.toStatesEmptyLabel.toEmptyLabel = .nonempty := by
  rcases ef with ef | _
  · rcases h with ⟨_, req⟩ | _
    · dsimp [ExecutionFragmentRaw.toStatesEmptyLabel]
      exact req.states_nonempty
  · dsimp [ExecutionFragmentRaw.toStatesEmptyLabel]

protected theorem states_length?_pos (h: ts.IsExecutionFragment ef) : 0 < ef.states.length? :=
  ef.toStatesEmptyLabel_toEmptyLabel_eq_states_toEmptyLabel.symm.trans h.states_nonempty |> Sequence.toEmptyLabel_eq_nonempty_iff_length?_pos.mp

theorem stepL
  (h: ts.IsExecutionFragment ef) (state0: ts.S) (action0: ts.Act)
  (req: state0 ─⌞action0⌟→{ts} (ef.state0 h.states_length?_pos))
  : ts.IsExecutionFragment (ef.stepL state0 action0) := by
  rcases ef with ef | ef
  · rcases h with ⟨_, lm1⟩ | _
    dsimp [ExecutionFragmentRaw.stepL]
    refine IsExecutionFragment.finite _ ?_
    refine lm1.stepL ?_
    exact req
  · rcases h with _ | ⟨_, lm1⟩
    dsimp [ExecutionFragmentRaw.stepL]
    refine IsExecutionFragment.infinite _ ?_
    refine lm1.stepL _ _ ?_
    exact req

theorem tail (h: ts.IsExecutionFragment ef) (req: ef.toActionsEmptyLabel.toEmptyLabel = .nonempty)
  : ts.IsExecutionFragment ef.tail := by
  rcases ef with ef | ef
  · rcases h with ⟨_, lm1⟩ | _
    dsimp [ExecutionFragmentRaw.tail]
    refine IsExecutionFragment.finite _ ?_
    refine lm1.tail ?_
    exact req
  · rcases h with _ | ⟨_, lm1⟩
    dsimp [ExecutionFragmentRaw.tail]
    refine IsExecutionFragment.infinite _ ?_
    exact lm1.tail


end IsExecutionFragment


@[ext]
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

/-
theorem ofSequence_isExecutionFragment : IsExecutionFragment (.ofSequence ef.states ef.actions ef.states_toLabel_eq_actions_toLabel) :=
  (IsExecutionFragment.ofSequence_eta_congr ef.states_toLabel_eq_actions_toLabel).mpr ef.is_valid
-/

theorem mk'_eta
  : (mk' ef.states ef.actions ef.states_toLabel_eq_actions_toLabel ef.is_valid.to_ofSequence_eta) = ef := by
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
  mk' t.states t.actions t.states_toLabel_eq_actions_toLabel t.is_valid.to_ofSequence_eta |> Eq.subst t.mk'_eta


def toSeqLabel : Sequence.Label := ef.raw.toSeqLabel


def ofFinite (ϱ: ts.FiniteExecutionFragment) : ts.ExecutionFragment :=
  ⟨.finite ϱ.raw, .finite ϱ.raw ϱ.is_valid⟩

@[defeq, simp]
theorem ofFinite_toSeqLabel {ϱ} : (@ofFinite ts ϱ).toSeqLabel = .finite := by
  dsimp [ofFinite, toSeqLabel]

def toFinite (req: ef.toSeqLabel = .finite) : ts.FiniteExecutionFragment :=
  ⟨ef.raw.toFinite req, (by
    rcases ef with ⟨raw, is_valid⟩
    cases raw
    · dsimp; cases is_valid; assumption
    · simp [toSeqLabel] at req )⟩

@[defeq, simp]
theorem ofFinite_toFinite {ϱ} : (@ofFinite ts ϱ).toFinite ofFinite_toSeqLabel = ϱ := rfl

theorem ofFinite_eta (req: ef.toSeqLabel = .finite) : (ofFinite (ef.toFinite req)) = ef := by
  rcases ef with ⟨raw, is_valid⟩
  cases raw
  · congr
  · simp [toSeqLabel] at req

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
theorem ofInfinite_toSeqLabel {ρ} : (@ofInfinite ts ρ).toSeqLabel = .infinite := by
  dsimp [ofInfinite, toSeqLabel]

def toInfinite (req: ef.toSeqLabel = .infinite) : ts.InfiniteExecutionFragment :=
  ⟨ef.raw.toInfinite req, (by
    rcases ef with ⟨raw, is_valid⟩
    cases raw
    · simp [toSeqLabel] at req
    · dsimp; cases is_valid; assumption )⟩

@[defeq, simp]
theorem ofInfinite_toInfinite {ρ} : (@ofInfinite ts ρ).toInfinite ofInfinite_toSeqLabel = ρ := rfl

theorem ofInfinite_eta (req: ef.toSeqLabel = .infinite) : (ofInfinite (ef.toInfinite req)) = ef := by
  rcases ef with ⟨raw, is_valid⟩
  cases raw
  · simp [toSeqLabel] at req
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
  match lm1: t.toSeqLabel with
  | .finite => finite (t.toFinite lm1) |> Eq.subst (t.ofFinite_eta lm1)
  | .infinite => infinite (t.toInfinite lm1) |> Eq.subst (t.ofInfinite_eta lm1)


@[defeq, simp]
theorem isFinite_indFiniteInfinite (req: ef.toSeqLabel = .finite) {motive finite infinite}
  : @indFiniteInfinite ts motive finite infinite ef = (finite (ef.toFinite req) |> Eq.subst (ef.ofFinite_eta req)) :=
  rfl

@[defeq, simp]
theorem isInfinite_indFiniteInfinite (req: ef.toSeqLabel = .infinite) {motive finite infinite}
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


def singleState (state0: ts.S) : ts.ExecutionFragment := ofFinite (.singleState state0)

@[defeq, simp]
theorem singleState_toLabel {state0} : (@singleState ts state0).toSeqLabel = .finite := by dsimp [singleState]

@[defeq, simp]
theorem singleState_actions_eq_nil {state0} : (@singleState ts state0).actions = Sequence.nil := rfl

@[defeq, simp]
theorem singleState_state0 {state0} : (@singleState ts state0).state0 = state0 := rfl

--open scoped EmptyLabel in
theorem singleState_eta (req: ef.actions.toEmptyLabel = .empty) : (.singleState ef.state0) = ef := by
  cases ef using indFiniteInfinite with
  | finite ϱ =>
    dsimp [singleState]
    congr
    refine FiniteExecutionFragment.singleState_eta _ ?_
    simp [EmptyLabel.ofList_eq_empty_iff_eq_nil]
    simpa [EmptyLabel.ofNat_empty_iff_eq_zero] using req
  | infinite _ => simp at req

/-
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
-/

/-
theorem ofFinite_actions_length_pos_iff {ϱ}
  : (0 < (@ofFinite ts ϱ).actions.length?) ↔ (0 < ϱ.actions.length) := by
  simp

theorem ofInfinite_actions_length_pos {ρ}
  : 0 < (@ofInfinite ts ρ).actions.length? := by
  simp
-/

def tail (req: ef.raw.toActionsEmptyLabel.toEmptyLabel = .nonempty) : ts.ExecutionFragment :=
  .mk ef.raw.tail (ef.is_valid.tail req)

/-
@[defeq, simp]
theorem ofFinite_tail {ϱ req} : ((@ofFinite ts ϱ).tail req) = (@ofFinite ts (ϱ.tail (ofFinite_actions_length_pos_iff.mp req))) := by
  dsimp [tail, Sequence.tail_finite]; rfl

@[defeq, simp]
theorem ofInfinite_tail {ρ} : (@ofInfinite ts ρ).tail ofInfinite_actions_length_pos = (@ofInfinite ts ρ.tail) := by
  dsimp [tail, Sequence.tail_infinite]; rfl
-/

def action0 (req: 0 < ef.actions.length?) : ts.Act := ef.actions[0]'(req)




/-
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
-/


def stepL (state0: ts.S) (action0: ts.Act) (req: state0 ─⌞action0⌟→{ts} ef.state0) : ts.ExecutionFragment :=
  .mk (ef.raw.stepL state0 action0) (ef.is_valid.stepL state0 action0 req)
/-
  .mk' (ef.states.cons state0) (ef.actions.cons action0)
    (ef.stepL_preserves_states_isFinite_eq_actions_isFinite) (ef.stepL_preserves_isExecutionFragment req)
-/

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
