module

public import Nemonuri.Executions.FiniteExecutionFragment.Raws
public import Nemonuri.Executions.InfiniteExecutionFragment.Raws

@[expose] public section

namespace Nemonuri.TransitionSystem


inductive ExecutionFragmentRaw (ts: TransitionSystem) where
  | finite (ϱ: ts.FiniteExecutionFragmentRaw)
  | infinite (ρ: ts.InfiniteExecutionFragmentRaw)

namespace ExecutionFragmentRaw

variable {ts: TransitionSystem} {ef: ts.ExecutionFragmentRaw}


def toLabel : ts.ExecutionFragmentRaw → Sequence.Label
  | .finite _ => .finite
  | .infinite _ => .infinite


@[defeq, simp]
theorem finite_toLabel {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).toLabel = .finite := rfl

@[defeq, simp]
theorem infinite_toLabel {ρ} : (@ExecutionFragmentRaw.infinite ts ρ).toLabel = .infinite := rfl

instance : HasLabel Sequence.Label ts.ExecutionFragmentRaw := ⟨toLabel⟩

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


section ToLabel

--@[simp]
theorem toLabel_eq_states_toLabel : ef.toLabel = ef.states.toLabel := by
  cases ef <;> simp

--@[simp]
theorem toLabel_eq_actions_toLabel : ef.toLabel = ef.actions.toLabel := by
  cases ef <;> simp

theorem states_toLabel_eq_actions_toLabel : ef.states.toLabel = ef.actions.toLabel := ef.toLabel_eq_states_toLabel.symm.trans ef.toLabel_eq_actions_toLabel

end ToLabel



def toExecutionLabel : ts.ExecutionFragmentRaw → ExecutionLabel
  | .finite ef => ef.toExecutionLabel
  | .infinite _ => .mk .nonempty .nonempty

section ToExecutionLabel

variable {ef: ts.ExecutionFragmentRaw}

@[defeq, simp]
theorem finite_toExecutionLabel {fef} : (@ExecutionFragmentRaw.finite ts fef).toExecutionLabel = fef.toExecutionLabel := rfl

@[defeq, simp]
theorem infinite_toExecutionLabel {ief} : (@ExecutionFragmentRaw.infinite ts ief).toExecutionLabel = .mk .nonempty .nonempty := rfl

@[simp]
theorem toExecutionLabel_states_eq_states_toEmptyLabel : ef.toExecutionLabel.states = ef.states.toEmptyLabel := by
  rcases ef with fef | ief
  · have lm1 := fef.toExecutionLabel_states_eq_states_ofList
    dsimp
    rw [lm1, EmptyLabel.ofList_eq_ofNat]
  · dsimp

@[simp]
theorem toExecutionLabel_actions_eq_actions_toEmptyLabel : ef.toExecutionLabel.actions = ef.actions.toEmptyLabel := by
  rcases ef with fef | ief
  · have lm1 := fef.toExecutionLabel_actions_eq_actions_ofList
    dsimp
    rw [lm1, EmptyLabel.ofList_eq_ofNat]
  · dsimp

end ToExecutionLabel

/-
theorem states_isFinite_eq_actions_isFinite (raw: ts.ExecutionFragmentRaw) : raw.states.isFinite = raw.actions.isFinite := by
  dsimp [states, actions]
  cases raw <;> simp
-/


def ofSequence
  (states: Sequence ts.S) (actions: Sequence ts.Act) (req: states.toLabel = actions.toLabel) : ts.ExecutionFragmentRaw :=
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
  : (ofSequence ef.states ef.actions ef.states_toLabel_eq_actions_toLabel) = ef := by
  dsimp [ExecutionFragmentRaw.ofSequence, states, actions]
  cases ef <;> simp


@[elab_as_elim]
def indOfSequence
  {motive: ts.ExecutionFragmentRaw → Sort _}
  (ofSequence: (states: Sequence ts.S) → (actions: Sequence ts.Act) → (req: states.toLabel = actions.toLabel) → motive (ExecutionFragmentRaw.ofSequence states actions req))
  (t: ts.ExecutionFragmentRaw)
  : motive t :=
  ofSequence t.states t.actions t.states_toLabel_eq_actions_toLabel |> Eq.subst ofSequence_eta

theorem ofSequence_ext_iff {raw1 raw2: ts.ExecutionFragmentRaw}
  : (raw1.states = raw2.states) ∧ (raw1.actions = raw2.actions) ↔ raw1 = raw2 := by
  constructor
  · cases raw1 using indOfSequence
    cases raw2 using indOfSequence
    simp
    intro lm1 lm2
    subst lm1; subst lm2; rfl
  · intro lm1; subst lm1; simp


/-
def isFinite : ts.ExecutionFragmentRaw → Bool
  | .finite _ => .true
  | .infinite _ => .false

@[simp, grind =]
theorem isFinite_finite {ϱ: ts.FiniteExecutionFragmentRaw} : isFinite (.finite ϱ) = .true := rfl

@[simp, grind =]
theorem isFinite_infinite {ρ: ts.InfiniteExecutionFragmentRaw} : isFinite (.infinite ρ) = .false := rfl
-/

def toFinite (ef: ts.ExecutionFragmentRaw) (req: ef.toLabel = .finite) : ts.FiniteExecutionFragmentRaw :=
  match ef with
  | .finite xs => xs
  | .infinite _ => absurd req (by simp)

@[defeq, simp]
theorem finite_toFinite {ϱ} : (@ExecutionFragmentRaw.finite ts ϱ).toFinite finite_toLabel = ϱ := rfl

/-
def isInfinite : ts.ExecutionFragmentRaw → Bool
  | .finite _ => .false
  | .infinite _ => .true

@[simp, grind =]
theorem isInfinite_finite {ϱ: ts.FiniteExecutionFragmentRaw} : isInfinite (.finite ϱ) = .false := rfl

@[simp, grind =]
theorem isInfinite_infinite {ρ: ts.InfiniteExecutionFragmentRaw} : isInfinite (.infinite ρ) = .true := rfl
-/

def toInfinite (ef: ts.ExecutionFragmentRaw) (req: ef.toLabel = .infinite) : ts.InfiniteExecutionFragmentRaw :=
  match ef with
  | .finite _ => absurd req (by simp)
  | .infinite xs => xs

@[defeq, simp]
theorem infinite_toInfinite {ρ} : (@ExecutionFragmentRaw.infinite ts ρ).toInfinite infinite_toLabel = ρ := rfl

/-
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
-/

@[defeq, simp]
theorem ofSequence_finite_toLabel {sts ats} : (@ofSequence ts (.finite sts) (.finite ats) rfl).toLabel = .finite := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_infinite_toLabel {sts ats} : (@ofSequence ts (.infinite sts) (.infinite ats) rfl).toLabel = .infinite := by
  dsimp [ofSequence]


@[defeq, simp]
theorem ofSequence_finite_toFinite {sts ats}
  : (@ofSequence ts (.finite sts) (.finite ats) rfl).toFinite ofSequence_finite_toLabel = ⟨sts, ats⟩ := by
  dsimp [ofSequence]

@[defeq, simp]
theorem ofSequence_infinite_toInfinite {sts ats}
  : (@ofSequence ts (.infinite sts) (.infinite ats) rfl).toInfinite ofSequence_infinite_toLabel = ⟨sts, ats⟩ := by
  dsimp [ofSequence]



structure IsPrefix (ef1: ts.FiniteExecutionFragmentRaw) (ef2: ts.ExecutionFragmentRaw) : Prop where
  states: ef2.states.IsPrefix ef1.states
  actions: ef2.actions.IsPrefix ef1.actions

namespace IsPrefix

variable {fef: ts.FiniteExecutionFragmentRaw} {ef: ts.ExecutionFragmentRaw} --(h: @IsPrefix ts fef ef) (n: Nat)

theorem lt_states_length?_of_lt_states_length (h: IsPrefix fef ef) {i: Nat} (req: i < fef.states.length) : i < ef.states.length? := by
  rcases h with ⟨lm1, _⟩
  refine lm1.lt_length?_of_lt_length ?_
  exact req

theorem states_getElem_eq (h: IsPrefix fef ef) {i: Nat} (req: i < fef.states.length)
  : fef.states[i]'(req) = ef.states[i]'(h.states.lt_length?_of_lt_length req) :=
  h.states.getElem_eq req

theorem states_getElem_eq' (h: IsPrefix fef ef) (i: Nat) (req: i < fef.states.length)
  : fef.states[i]'(req) = ef.states[i]'(h.states.lt_length?_of_lt_length req) :=
  @h.states_getElem_eq _ _ _ i req


theorem lt_actions_length?_of_lt_actions_length (h: IsPrefix fef ef) {i: Nat} (req: i < fef.actions.length) : i < ef.actions.length? := by
  rcases h with ⟨_, lm1⟩
  refine lm1.lt_length?_of_lt_length ?_
  exact req

theorem actions_getElem_eq (h: IsPrefix fef ef) {i: Nat} (req: i < fef.actions.length)
  : fef.actions[i]'(req) = ef.actions[i]'(h.actions.lt_length?_of_lt_length req) :=
  h.actions.getElem_eq req

end IsPrefix



structure IsSuffix (ef1: ts.FiniteExecutionFragmentRaw) (ef2: ts.ExecutionFragmentRaw) : Prop where
  states: ef2.states.IsSuffix ef1.states
  actions: ef2.actions.IsSuffix ef1.actions

end ExecutionFragmentRaw


end Nemonuri.TransitionSystem

end
