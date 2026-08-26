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

/-
section Notation

syntax:40 " 𝒰 " term:40 : term

macro_rules
  | `(𝒰 $α) => ``((Finset.univ : Finset $α))

end Notation
-/

/-
def attachUniv (α: Type _) [Fintype α] : α ↪ (𝒰 α) where
  toFun a := ⟨a, Finset.mem_univ a⟩
  inj' a1 a2 := by simp

def attachUnivToFinset (α: Type _) [Fintype α] : Finset α ↪o Finset (𝒰 α) :=
  Finset.mapEmbedding (attachUniv α)
-/

open PropositionalLogics Formula


structure TransitionSystem.{u1, u2, u3} where
  /-- A set of states -/
  S: Type u1
  /-- A set of actions -/
  Act: Type u2
  /-- A transition relation -/
  tr: S → Act → S → Prop
  /-- a set of initial states -/
  I: Set S
  /-- a set of atomic propositions -/
  AP: Type u3
  /-- a labeling function -/
  L: S → AP → Bool --𝒫 (.univ : Set AP)

--attribute [simp low] TransitionSystem.S TransitionSystem.Act

namespace TransitionSystem



def labeling (ts: TransitionSystem) (s: ts.S) : ts.AP → Bool := ts.L s

def LabelingEquiv (ts: TransitionSystem) (s1 s2: ts.S) : Prop := ts.labeling s1 = ts.labeling s2

section Labeling

variable {ts: TransitionSystem} {s1 s2: ts.S}

theorem labelingEquiv_iff_forall_ap : (ts.LabelingEquiv s1 s2) ↔ ∀(ap: ts.AP), ts.labeling s1 ap = ts.labeling s2 ap := by
  dsimp [LabelingEquiv]
  simp [funext_iff]

namespace LabelingEquiv

theorem equivalence : Equivalence ts.LabelingEquiv := by
  constructor
  · intro _; dsimp [LabelingEquiv]
  · intro _ _ lm1;
    dsimp [LabelingEquiv] at lm1 ⊢
    exact lm1.symm
  · dsimp [LabelingEquiv]
    intro _ _ _ lm1 lm2
    exact lm1.trans lm2

end LabelingEquiv

@[reducible]
def toLabelingSetoid (ts: TransitionSystem) : Setoid ts.S where
  r := ts.LabelingEquiv
  iseqv := LabelingEquiv.equivalence


def toLabelingQuotient (ts: TransitionSystem) (s: ts.S) : Quotient ts.toLabelingSetoid := Quotient.mk ts.toLabelingSetoid s



end Labeling



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

namespace ConcreteFinite

variable {ts: TransitionSystem} [ConcreteFinite ts]



instance (priority := low) decidableEqOfForallAPBool : DecidableEq (ts.AP → Bool) := Fintype.decidablePiFintype

instance (priority := low) decidableLabelingEquiv : DecidableRel (ts.LabelingEquiv) :=
  fun s1 s2 => decidable_of_iff (ts.labeling s1 = ts.labeling s2) (by dsimp [LabelingEquiv]; rfl)

instance (priority := low) decidableEqOfLabelingQuotient : DecidableEq (Quotient ts.toLabelingSetoid) :=
  @Quotient.decidableEq ts.S ts.toLabelingSetoid (inferInstanceAs (DecidableRel (ts.LabelingEquiv)))


end ConcreteFinite



variable (ts: TransitionSystem)

abbrev lts : Cslib.LTS ts.S ts.Act := ⟨ts.tr⟩


section Notation

syntax:52 term:53 " ─⌞" term "⌟→{ " term " } " term:52 : term

macro_rules
  | `( $s1 ─⌞ $act ⌟→{ $ts } $s2 ) => ``( Cslib.LTS.Tr (TransitionSystem.lts $ts) $s1 $act $s2 )


end Notation


variable [ConcreteFinite ts]

/-
protected abbrev univ : Finset ts.AP := @Finset.univ _ (@ConcreteFinite.fintypeAP ts _)

@[defeq] theorem univ_eq : ts.univ = Finset.univ := rfl
-/

/-
/-- Not always injective -/
def evalStateToBoolPred (s: ts.S) : ts.AP → Bool :=
  ts.L s

@[reducible]
def evalStateKernel : Setoid ts.S := Setoid.ker ts.evalStateToBoolPred

omit [ts.ConcreteFinite] [IsStateSpaceValid ts] in
@[defeq] theorem evalStateKernel_eq_ker : Quotient ts.evalStateKernel = Quotient (Setoid.ker ts.evalStateToBoolPred) := rfl
-/


--set_option trace.Meta.synthInstance true in
instance : EvalLike (Quotient ts.toLabelingSetoid) ts.AP where
  coe s := Quotient.liftOn s (Eval.mk ∘ ts.labeling) (by
    intro s1 s2 lm1
    change ts.LabelingEquiv s1 s2 at lm1
    dsimp [LabelingEquiv] at lm1
    simpa using lm1 )
  coe_injective s1 s2 := by
    cases s1 using Quotient.inductionOn
    cases s2 using Quotient.inductionOn
    simp
    intro lm1
    simp [funext_iff] at lm1
    apply Quotient.sound
    change ts.LabelingEquiv _ _
    ext x; exact lm1 x

    --dsimp [Function.RightInverse, Function.LeftInverse] at lm2

    --have lm2 := lm1.surjective
    --refine funext ?_
    --intro ap
    --specialize lm1 ev
    --exact lm1
/-
    simp [toLabelingQuotient]
    simp [funext_iff] at lm2 ⊢
    exact lm2 ev
-/

/-

    exists ts.toLabelingQuotient (finv ev)
    simp [toLabelingQuotient]
    exact lm2.symm
-/
/-
    simp
    obtain ⟨f, lm2⟩ := (inferInstance: ts.IsStateSpaceValid).surjection_exists
    obtain ⟨s, lm3⟩ := @lm2 ev
    exists Quotient.mk ts.evalStateKernel s
    simp
    dsimp [evalStateToBoolPred]
    simp only [funext_iff]
    intro ap
-/

/-
instance (priority := low) : Formula.HasEvalLike ts.AP where
  Carrier := (Quotient ts.toLabelingSetoid)
-/

section Notation

syntax:51 " ⟦" term "⟧{" term "} " : term

macro_rules
  | `( ⟦ $s ⟧{ $ts } ) => ``( toLabelingQuotient $ts $s )

end Notation


/-- Not always injective -/
def evalStateToFinset (s: ts.S) : Finset (ts.AP) := (Indicator.mk (ts.labeling s)).toFinset

section Notation

syntax:51 " 𝐿{" term "}⸨ " term " ⸩" : term

macro_rules
  | `( 𝐿{ $ts }⸨ $s ⸩ ) => ``( evalStateToFinset $ts $s )

end Notation


@[scoped grind =]
theorem isSat_iff [DecidableEq ts.AP] (p: Formula ts.AP) (s: ts.S)
  : ⟦s⟧{ts} ⊨ₚ p ↔ 𝐿{ts}⸨s⸩ ⊨ₚ p := by
  dsimp [SatRel.IsSat, DFunLike.coe, SatRel.defaultAt, Inhabited.default, SatRel.default]
  refine propext_iff.mp ?_
  refine congrFun ?_ p
  refine congrArg _ ?_
  dsimp [EvalLike.toIndicator, EvalLike.coe]
  dsimp [toLabelingQuotient]
  refine DFunLike.ext'_iff.mp ?_
  refine congrArg Eval.mk ?_
  refine funext ?_
  intro ap
  dsimp [evalStateToFinset, Indicator.fn, Indicator.mk]
  dsimp [labeling]
  simp [Indicator.ofFinset_toFinset_leftInverse.eq]



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
  post_subsingleton (s: ts.S) (A: ts.AP → Bool) : ((𝑃𝑜𝑠𝑡{ts}⸨s⸩) ∩ { s': ts.S | (𝐿{ts}⸨s'⸩) = { ap | A ap = .true } }).Subsingleton





end TransitionSystem


end Nemonuri

end
