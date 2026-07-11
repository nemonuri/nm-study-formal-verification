module


public import Mathlib.Data.Finite.Defs
public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Relation
import Cslib.Foundations.Semantics.LTS.Notation
public import Nemonuri.PropositionalLogics

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

def lts : Cslib.LTS ts.S ts.Act := ⟨ts.tr⟩

instance : CoeDep TransitionSystem ts (Cslib.LTS ts.S ts.Act) := ⟨ts.lts⟩


variable [ConcreteFinite ts]



scoped instance (α: Sort _) : FunLike (ts.AP → α) (𝒰 ts.AP) α where
  coe f e := f e
  coe_injective f1 f2 := by
    simp only
    intro lm1
    simp [funext_iff] at lm1
    ext a
    exact lm1 a


/-- Not always injective -/
def evalStateToBoolPred (s: ts.S) : (𝒰 ts.AP) → Bool :=
  ts.L s

instance : CoeOut ts.S (Eval (𝒰 ts.AP)) where
  coe s := ts.evalStateToBoolPred s


/-- Not always injective -/
def evalStateToFinset (s: ts.S) : Finset (𝒰 ts.AP) := { ap : 𝒰 ts.AP | ts.L s ap = .true }

section Notation

syntax:30 " 𝐿{" term "}( " term " )" : term

macro_rules
  | `( 𝐿{ $ts }( $s ) ) => ``( evalStateToFinset $ts $s )


end Notation

@[scoped grind =]
theorem isSat_iff [DecidableEq ts.AP] (p: Formula (𝒰 ts.AP)) (s: ts.S) (sr: SatRel (𝒰 ts.AP))
  : s ⊨ₚ{sr} p ↔ (𝐿{ts}(s)) ⊨ₚ{sr} p := by
  apply propext_iff.mp
  refine congrArg₂ (IsSat sr) ?_ rfl
  simp only [evalStateToBoolPred, evalStateToFinset]
  refine Eq.trans (Eval.mk _ |> Eq.refl) ?_
  refine Eq.trans ?_ (Eval.ofSubset _ |> Eq.refl)
  simp only [Eval.ofSubset]
  simp
  rfl

/-
theorem evalState_injective : Function.Injective (ts.evalState) := by
  intro s1 s2
  simp [evalState]
  intro lm1
  simp [funext_iff] at lm1
-/


--theorem toFinite (h1: Finite ts.S) (h2: Finite ts.Act) (h3: Finite ts.AP) : Fini



end TransitionSystem


end Nemonuri

end
