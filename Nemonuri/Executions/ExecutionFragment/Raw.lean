module

public import Nemonuri.Executions.FiniteExecutionFragment.Raw
public import Nemonuri.Executions.InfiniteExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem


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

end ExecutionFragmentRaw


end Nemonuri.TransitionSystem

end
