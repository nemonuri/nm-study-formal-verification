module


public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Setoid.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Relation
import Cslib.Foundations.Semantics.LTS.Notation
public import Nemonuri.PropositionalLogics
public import Cslib.Foundations.Semantics.LTS.Execution
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1 Transition Systems, p.19

-/

@[expose] public section

namespace Nemonuri

section Notation

syntax:40 " 𝒰 " term:40 : term

macro_rules
  | `(𝒰 $α) => ``((Finset.univ : Finset $α))

end Notation

/-
def attachUniv (α: Type _) [Fintype α] : α ↪ (𝒰 α) where
  toFun a := ⟨a, Finset.mem_univ a⟩
  inj' a1 a2 := by simp

def attachUnivToFinset (α: Type _) [Fintype α] : Finset α ↪o Finset (𝒰 α) :=
  Finset.mapEmbedding (attachUniv α)
-/

open PropositionalLogics Formula SatRel IsSat

structure TransitionSystem where
  /-- A set of states -/
  S: Type _
  /-- A set of actions -/
  Act: Type _
  /-- A transition relation -/
  tr: S → Act → S → Prop
  /-- a set of initial states -/
  I: Set S
  /-- a set of atomic propositions -/
  AP: Type _
  /-- a labeling function -/
  L: S → AP → Bool --𝒫 (.univ : Set AP)

namespace TransitionSystem

/-- `TS` is called finite if `S`, `Act`, and `AP` are finite. -/
@[mk_iff]
structure IsFinite (TS: TransitionSystem) : Prop where
  finite_s: Finite TS.S
  finite_act: Finite TS.Act
  finite_ap: Finite TS.AP

class ConcreteFinite (TS: TransitionSystem) where
  fintypeS: Fintype TS.S
  fintypeAct: Fintype TS.Act
  fintypeAP: Fintype TS.AP

attribute [reducible, instance] ConcreteFinite.fintypeS
attribute [reducible, instance] ConcreteFinite.fintypeAct
attribute [reducible, instance] ConcreteFinite.fintypeAP


variable (ts: TransitionSystem)

abbrev lts : Cslib.LTS ts.S ts.Act := ⟨ts.tr⟩


section Notation

syntax:52 term:53 " ─⌞" term "⌟→{ " term " } " term:52 : term

macro_rules
  | `( $s1 ─⌞ $act ⌟→{ $ts } $s2 ) => ``( Cslib.LTS.Tr (TransitionSystem.lts $ts) $s1 $act $s2 )


end Notation


variable [ConcreteFinite ts]


protected abbrev univ : Finset ts.AP := @Finset.univ _ (@ConcreteFinite.fintypeAP ts _)

@[defeq] theorem univ_eq : ts.univ = Finset.univ := rfl


/-- Not always injective -/
def evalStateToBoolPred (s: ts.S) : ts.AP → Bool :=
  ts.L s

@[reducible]
def evalStateKernel : Setoid ts.S := Setoid.ker ts.evalStateToBoolPred

omit [ts.ConcreteFinite] in
@[defeq] theorem evalStateKernel_eq_ker : Quotient ts.evalStateKernel = Quotient (Setoid.ker ts.evalStateToBoolPred) := rfl


instance : Eval.EvalLike (Quotient ts.evalStateKernel) ts.univ where
  coe s := Quotient.liftOn s (Eval.mk ∘ (fun f x => f x.val) ∘ ts.evalStateToBoolPred) (by
    simp
    intro s1 s2 lm1
    simp [funext_iff] at lm1
    ext x; exact lm1 x.val )
  coe_injective s1 s2 := by
    cases s1 using Quotient.inductionOn
    cases s2 using Quotient.inductionOn
    simp
    intro lm1
    simp [funext_iff] at lm1
    apply Quotient.sound
    simp
    ext x; exact lm1 x


section Notation

syntax:51 " ⟦" term "⟧{" term "} " : term

macro_rules
  | `( ⟦ $s ⟧{ $ts } ) => ``( Quotient.mk (evalStateKernel $ts) $s )

end Notation


/-- Not always injective -/
def evalStateToFinset (s: ts.S) : Finset (ts.AP) := { ap : ts.AP | ts.L s ap = .true }

section Notation

syntax:51 " 𝐿{" term "}⸨ " term " ⸩" : term

macro_rules
  | `( 𝐿{ $ts }⸨ $s ⸩ ) => ``( evalStateToFinset $ts $s )

end Notation


@[scoped grind =]
theorem isSat_iff [DecidableEq ts.AP] (p: Formula ts.univ) (s: ts.S) (sr: SatRel ts.univ)
  : ⟦s⟧{ts} ⊨ₚ{sr} p ↔ 𝐿{ts}⸨s⸩ ⊨ₚ{sr} p := by
  revert p sr; dsimp only [univ_eq]; intro p sr
  apply propext_iff.mp
  refine congrArg₂ (IsSat sr) ?_ rfl
  refine Eq.trans (Eval.mk _ |> Eq.refl) ?_
  refine Eq.trans ?_ (Eval.ofSubset _ |> Eq.refl)
  simp [evalStateToBoolPred, evalStateToFinset, Eval.ofSubset]


/-!

### Definition 2.3. Direct Predecessors and Successors

-/


def SetOfDirectSuccessorAt (s: ts.S) (α: ts.Act) : Set ts.S := { s': ts.S | s ─⌞α⌟→{ts} s' }

def SetOfDirectPredecessorAt (s: ts.S) (α: ts.Act) : Set ts.S := { s': ts.S | s' ─⌞α⌟→{ts} s }

section Notation

syntax:61 " 𝑃𝑜𝑠𝑡{" term "}⸨" term "," term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒{" term "}⸨" term "," term "⸩ " : term

macro_rules
  | `( 𝑃𝑜𝑠𝑡{ $ts }⸨ $s , $α ⸩ ) => ``( SetOfDirectSuccessorAt $ts $s $α )
  | `( 𝑃𝑟𝑒{ $ts }⸨ $s , $α ⸩ ) => ``( SetOfDirectPredecessorAt $ts $s $α )

end Notation


def SetOfDirectSuccessor (s: ts.S) : Set ts.S := ⋃ α: ts.Act, 𝑃𝑜𝑠𝑡{ts}⸨s, α⸩

def SetOfDirectPredecessor (s: ts.S) : Set ts.S := ⋃ α: ts.Act, 𝑃𝑟𝑒{ts}⸨s, α⸩


section Notation

syntax:61 " 𝑃𝑜𝑠𝑡{" term "}⸨" term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒{" term "}⸨" term "⸩ " : term

macro_rules
  | `( 𝑃𝑜𝑠𝑡{ $ts }⸨ $s ⸩ ) => ``( SetOfDirectSuccessor $ts $s )
  | `( 𝑃𝑟𝑒{ $ts }⸨ $s ⸩ ) => ``( SetOfDirectPredecessor $ts $s )

end Notation


def UnionOfDirectSuccessorAt (C: Set ts.S) (α: ts.Act) : Set ts.S := ⋃ s ∈ C, 𝑃𝑜𝑠𝑡{ts}⸨s, α⸩

def UnionOfDirectPredecessorAt (C: Set ts.S) (α: ts.Act) : Set ts.S := ⋃ s ∈ C, 𝑃𝑟𝑒{ts}⸨s, α⸩

def UnionOfDirectSuccessor (C: Set ts.S) : Set ts.S := ⋃ s ∈ C, 𝑃𝑜𝑠𝑡{ts}⸨s⸩

def UnionOfDirectPredecessor (C: Set ts.S) : Set ts.S := ⋃ s ∈ C, 𝑃𝑟𝑒{ts}⸨s⸩


section Notation

syntax:61 " 𝑃𝑜𝑠𝑡ᵤ{" term "}⸨" term "," term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒ᵤ{" term "}⸨" term "," term "⸩ " : term
syntax:61 " 𝑃𝑜𝑠𝑡ᵤ{" term "}⸨" term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒ᵤ{" term "}⸨" term "⸩ " : term

macro_rules
  | `( 𝑃𝑜𝑠𝑡ᵤ{ $ts }⸨ $C, $α ⸩ ) => ``( UnionOfDirectSuccessorAt $ts $C $α )
  | `( 𝑃𝑟𝑒ᵤ{ $ts }⸨ $C, $α ⸩ ) => ``( UnionOfDirectPredecessorAt $ts $C $α )
  | `( 𝑃𝑜𝑠𝑡ᵤ{ $ts }⸨ $C ⸩ ) => ``( UnionOfDirectSuccessor $ts $C )
  | `( 𝑃𝑟𝑒ᵤ{ $ts }⸨ $C ⸩ ) => ``( UnionOfDirectPredecessor $ts $C )

end Notation


/-!

### Definition 2.4. Terminal State

-/

def IsTerminal (s: ts.S) : Prop := 𝑃𝑜𝑠𝑡{ts}⸨s⸩ = ∅


/-!

### Definition 2.5. Deterministic Transition System

-/

structure IsActionDeterministic (ts: TransitionSystem) : Prop where
  initial_subsingleton : ts.I.Subsingleton
  post_subsingleton (s: ts.S) (α: ts.Act) : (𝑃𝑜𝑠𝑡{ts}⸨s, α⸩).Subsingleton

structure IsAPDeterministic (ts: TransitionSystem) [ConcreteFinite ts] : Prop where
  initial_subsingleton : ts.I.Subsingleton
  post_subsingleton (s: ts.S) (A: ts.AP → Bool) : ((𝑃𝑜𝑠𝑡{ts}⸨s⸩) ∩ { s': ts.S | (𝐿{ts}⸨s'⸩) = A }).Subsingleton


/-!

### Definition 2.6. Execution Fragment

-/

structure FiniteExecutionFragmentRaw (ts: TransitionSystem) where
  firstState: ts.S
  actions: List ts.Act
  lastState: ts.S
  states: List ts.S

@[mk_iff]
structure IsFiniteExecutionFragment (raw: ts.FiniteExecutionFragmentRaw) : Prop where
  length_eq : raw.states.length = raw.actions.length + 1
  firstState_eq : raw.states[0] = raw.firstState
  lastState_eq : raw.states[raw.states.length - 1] = raw.lastState
  states_actions_valid (i: Nat) (h: i < raw.actions.length) : raw.states[i] ─⌞(raw.actions[i])⌟→{ts} raw.states[i+1]

open Cslib.LTS in
omit [ts.ConcreteFinite] in
theorem isFiniteExecutionFragment_iff_execution (raw: ts.FiniteExecutionFragmentRaw)
  : ts.IsFiniteExecutionFragment raw ↔ ts.lts.Execution raw.firstState raw.actions raw.lastState raw.states := by
  dsimp only [Execution]
  constructor
  · intro lm1
    exact ⟨lm1.length_eq, lm1.firstState_eq, lm1.lastState_eq, lm1.states_actions_valid⟩
  · rintro ⟨length_eq, firstState_eq, lastState_eq, states_actions_valid⟩
    exact IsFiniteExecutionFragment.mk length_eq firstState_eq lastState_eq states_actions_valid

/-
def IsFiniteExecutionFragment (raw: ts.FiniteExecutionFragmentRaw) : Prop :=
  ts.lts.Execution raw.firstState raw.actions raw.lastState raw.states
-/

structure FiniteExecutionFragment (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: ts.IsFiniteExecutionFragment raw


namespace FiniteExecutionFragment


variable {ts: TransitionSystem} (ϱ: ts.FiniteExecutionFragment)


theorem raw_states_ne_nil : ϱ.raw.states ≠ [] := List.ne_nil_of_length_eq_add_one ϱ.is_valid.length_eq


protected def firstState : ts.S := ϱ.raw.firstState

theorem firstState_eq_head : ϱ.firstState = ϱ.raw.states.head ϱ.raw_states_ne_nil := by
  rcases ϱ with ⟨raw, is_valid⟩
  dsimp [FiniteExecutionFragment.firstState]
  simp only [List.head_eq_getElem]
  exact is_valid.firstState_eq.symm



protected def lastState : ts.S := ϱ.raw.lastState

theorem lastState_eq_getLast : ϱ.lastState = ϱ.raw.states.getLast ϱ.raw_states_ne_nil := by
  rcases ϱ with ⟨raw, is_valid⟩
  dsimp [FiniteExecutionFragment.lastState]
  simp only [List.getLast_eq_getElem]
  exact is_valid.lastState_eq.symm


def length : Nat := ϱ.raw.actions.length

@[defeq] theorem length_eq_actions_length : ϱ.length = ϱ.raw.actions.length := rfl

theorem zero_lt_states_length : (0 < ϱ.raw.states.length) :=
  calc
    0 < _ := Nat.add_one_pos _
    _ = _ := ϱ.is_valid.length_eq.symm

theorem firstState_eq_getElem : ϱ.firstState = ϱ.raw.states[0]'(ϱ.zero_lt_states_length) := by
  dsimp [FiniteExecutionFragment.firstState]
  exact ϱ.is_valid.firstState_eq.symm

theorem states_length_lt_states_sub_one : ϱ.raw.states.length - 1 < ϱ.raw.states.length :=
  Nat.sub_lt ϱ.zero_lt_states_length Nat.zero_lt_one


theorem lastState_eq_getElem : ϱ.lastState = ϱ.raw.states[ϱ.raw.states.length - 1]'(ϱ.states_length_lt_states_sub_one) := by
  dsimp [FiniteExecutionFragment.lastState]
  exact ϱ.is_valid.lastState_eq.symm

theorem length_eq_states_length_sub_one : ϱ.length = ϱ.raw.states.length - 1 :=
  calc
    ϱ.length = _ := ϱ.length_eq_actions_length
    _ = _ := by simp [ϱ.is_valid.length_eq]


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

structure StepLEntry (ts : TransitionSystem) where
  ϱ: ts.FiniteExecutionFragment
  s: ts.S
  act: ts.Act
  req: s ─⌞act⌟→{ts} ϱ.firstState


protected def stepLInv (req: 0 < ϱ.length) : StepLEntry ts :=
  have lm1 := ϱ.length_eq_actions_length ▸ req
  have lm2 : 1 < ϱ.raw.states.length := by have _ := ϱ.length_eq_states_length_sub_one ▸ req; omega
  {
    ϱ := {
      raw := {
        firstState := ϱ.raw.states[1]'(lm2)
        actions := ϱ.raw.actions.tail
        lastState := ϱ.lastState
        states := ϱ.raw.states.tail
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
          refine ϱ.is_valid.states_actions_valid (i+1) ?_
        · dsimp; simp only [List.length_tail]
          rw [ϱ.is_valid.length_eq]
          omega
    }
    s := ϱ.firstState
    act := ϱ.raw.actions[0]'(lm1)
    req := by
      dsimp [FiniteExecutionFragment.firstState]
      rw [← ϱ.is_valid.firstState_eq]
      exact ϱ.is_valid.states_actions_valid 0 lm1
  }







--protected def stepLInv (req: 0 < ϱ.length) : Σ' (ϱ': ts.FiniteExecutionFragment) (s: ts.S) (act: ts.Act), (s ─⌞act⌟→{ts} ϱ'.firstState) :=
--∑(ϱ': ts.FiniteExecutionFragment), ∑(s: ts.S), ∑(act: ts.Act), (s ─⌞act⌟→{ts} ϱ'.firstState) :=


/-
theorem length_ne_zero_iff_stepL_eq
  : (ϱ.length ≠ 0) ↔ (∃(ϱ': ts.FiniteExecutionFragment), ∃ s act req, ϱ = ϱ'.stepL s act req) := by
  simp only [Nat.ne_zero_iff_zero_lt]
  constructor
  · intro lm1
-/





/-
@[elab_as_elim, induction_eliminator]
protected def ind
  {motive : ts.FiniteExecutionFragment → Sort _}
  (refl: (s: ts.S) → motive <| FiniteExecutionFragment.refl ts s )
  (stepL: (ϱ : ts.FiniteExecutionFragment) → (s: ts.S) → (act: ts.Act) → (req: s ─⌞act⌟→{ts} ϱ.firstState) → motive <| ϱ.stepL s act req)
  (t: ts.FiniteExecutionFragment)
  : motive t :=
  match eq1: t.raw.actions with
  | .nil => refl (t.firstState) |> cast (by
      refine congrArg motive ?_
      dsimp [FiniteExecutionFragment.refl]
      have lm2 := t.actions_eq_nil_iff_states_eq_singleton.mp eq1
      simp only [← lm2]
      have lm3 := t.actions_eq_nil_imp_firstState_eq_lastState eq1
      conv => lhs; arg 1; arg 3; rw [lm3]
      conv => lhs; arg 1; arg 2; rw [← eq1]
      dsimp only [FiniteExecutionFragment.firstState, FiniteExecutionFragment.lastState]
    )
  | .cons hd tl => stepL
-/





structure ActionList (ϱ: ts.FiniteExecutionFragment) where
  toList: List ts.Act
  is_valid: toList = ϱ.raw.actions

def actions : ActionList ϱ := .mk ϱ.raw.actions rfl

def IsValidStateIndex (idx: Nat) : Prop := idx ≤ ϱ.length

def IsValidActionIndex (idx: Nat) : Prop := (0 < idx) ∧ (ϱ.IsValidStateIndex idx)


namespace ActionList

variable {ϱ: ts.FiniteExecutionFragment}

/-
def getAt (as: ActionList ϱ) (idx: Nat) (req: ϱ.IsValidActionIndex idx) : ts.Act :=
  as.toList.get ⟨idx, (by
    rcases as with ⟨toList, is_valid⟩
    dsimp [IsValidActionIndex, IsValidStateIndex, FiniteExecutionFragment.length] at req
    subst is_valid
    simp only
  )⟩
-/


end ActionList


structure StateList (ϱ: ts.FiniteExecutionFragment) where
  toList: List ts.S
  is_valid: toList = ϱ.raw.states

def states : StateList ϱ := .mk ϱ.raw.states rfl



end FiniteExecutionFragment







end TransitionSystem


end Nemonuri

end
