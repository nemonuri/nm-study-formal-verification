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





end TransitionSystem


end Nemonuri

end
