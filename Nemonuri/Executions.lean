module

public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Nemonuri.Executions.FiniteExecutionFragment
public import Nemonuri.Executions.InfiniteExecutionFragment

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1.1 Executions, p.24

-/


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

section Definition

variable {ts: TransitionSystem}


inductive IsExecutionFragment : ts.ExecutionFragmentRaw → Prop where
  | finite (raw: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment raw) : IsExecutionFragment (.finite raw)
  | infinite (raw: ts.InfiniteExecutionFragmentRaw) (req: ts.IsInfiniteExecutionFragment raw) : IsExecutionFragment (.infinite raw)

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
