module

public import Nemonuri.TransitionSystemLike.Basic

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 32

-/

@[expose] public section

namespace Nemonuri

namespace ProgramGraph

structure Eval (Var Val: Type*) where
  eval: Var → Val

instance {Var Val: Type*} : FunLike (Eval Var Val) Var Val where
  coe ev := ev.eval
  coe_injective := by rintro ⟨_⟩ ⟨_⟩; simp


class EvalLike (EC: Type*) (Var Val: outParam Type*) where
  protected coe: EC → Eval Var Val
  coe_injective: Function.Injective coe

attribute [coe, reducible] EvalLike.coe

instance {EC Var Val: Type*} [EvalLike EC Var Val] : CoeOut EC (Eval Var Val) := ⟨EvalLike.coe⟩


structure StandardType (EC Var Val: Type*) [EvalLike EC Var Val] where
  dom : Var → Set Val
  valid (ec: EC) (v: Var) : ((ec: Eval Var Val) v) ∈ (dom v)

namespace StandardType

variable {EC Var Val: Type*} [EvalLike EC Var Val]

def IsSafe (sty: StandardType EC Var Val) (v: Var) (D: Set Val) : Prop := D ⊆ sty.dom v

abbrev DecidableSafe (sty: StandardType EC Var Val) : Type _ := (v: Var) → (D: Set Val) → Decidable (sty.IsSafe v D)


structure AtomicProp (sty: StandardType EC Var Val) where
  var: Var
  indicate: Val → Bool
  valid: sty.IsSafe var { val | indicate val = .true }


def indicateAtomicProp (sty: StandardType EC Var Val) (ec: EC) (ap: sty.AtomicProp) : Bool :=
  ap.indicate ((ec: Eval Var Val) ap.var)

/-
def indicateAtomicProp_injective (sty: StandardType EC Var Val) : Function.Injective (sty.indicateAtomicProp) := by
  intro ec1 ec2 lm1
  simp only [funext_iff, indicateAtomicProp] at lm1
  rw [← EvalLike.coe_injective.eq_iff, ← DFunLike.coe_injective.eq_iff, funext_iff]
  intro v
-/


namespace AtomicProp

variable {EC Var Val: Type*} [EvalLike EC Var Val]
         [Fintype Var] [Fintype Val] [DecidableEq Val]
         {sty: StandardType EC Var Val} [sty.DecidableSafe]

abbrev SubProd (sty: StandardType EC Var Val) : Type _ := { x: (Var × (Val → Bool)) // sty.IsSafe x.fst { val | x.snd val = .true } }

scoped instance (priority := low) fintypeOfSubProd : Fintype (SubProd sty) :=
  let dp : DecidablePred (fun (x: (Var × (Val → Bool))) => sty.IsSafe x.fst { val | x.snd val = .true }) := inferInstance
  let ft : Fintype ((Var × (Val → Bool))) := inferInstance
  @Subtype.fintype _ (fun (x: (Var × (Val → Bool))) => sty.IsSafe x.fst { val | x.snd val = .true }) dp ft


def toSubProd (ap: sty.AtomicProp) : SubProd sty :=
  ⟨(ap.var, ap.indicate), ap.valid⟩

def ofSubProd (sp: SubProd sty) : sty.AtomicProp :=
  .mk sp.val.fst sp.val.snd sp.property

def equivToSubProd : sty.AtomicProp ≃ SubProd sty where
  toFun := toSubProd
  invFun := ofSubProd

instance toFintype : Fintype (sty.AtomicProp) := Fintype.ofEquiv (SubProd sty) equivToSubProd.symm


end AtomicProp

/-
@[reducible]
def toIndicatorLike [Fintype Var] [Fintype Val] [DecidableEq Val] (sty: StandardType EC Var Val) [sty.DecidableSafe] : PropositionalLogics.EvalLike EC (sty.AtomicProp) where
  coe ec := sty.indicateAtomicProp ec |> .mk
  coe_injective := by
-/



inductive IsCond (sty: StandardType EC Var Val) : List (Var × Set Val) → Prop where
  | nil : IsCond sty []
  | cons (v: Var) (D: Set Val) (req1: sty.IsSafe v D) (fml: List (Var × Set Val)) (req2: IsCond sty fml) : IsCond sty ((v, D) :: fml)

attribute [simp] IsCond.nil

end StandardType


structure Cond (EC Var Val: Type*) [EvalLike EC Var Val] (sty: StandardType EC Var Val) where
  formula: List (Var × Set Val)
  valid (ec: EC) : sty.IsCond formula


class CondLike (CC EC Var Val: Type*) [EvalLike EC Var Val] where
  standardType: StandardType EC Var Val
  toCond: CC → Cond EC Var Val standardType
  toCond_Injective: Function.Injective toCond


end ProgramGraph

/-!

### Definition 2.13. Program Graph (PG)

-/


open ProgramGraph in
structure ProgramGraph (CC EC Var Val: Type*) [EvalLike EC Var Val] [CondLike CC EC Var Val] where
  Loc: Type*
  Act: Type*
  effect: Act → EC → EC
  ctr: Loc → CC → Act → Loc → Prop
  loc0: Loc → Prop
  g0: Cond EC Var Val (CondLike.standardType CC)


/-!

### Definition 2.15. Transition System Semantics of a Program Graph

-/

namespace ProgramGraph

variable {CC EC Var Val: Type*} [EvalLike EC Var Val] [CondLike CC EC Var Val]

def Loc0 (pg: ProgramGraph CC EC Var Val) : Set (pg.Loc) := { l | pg.loc0 l }

@[reducible]
def toTransitionSystem (pg: ProgramGraph CC EC Var Val) : TransitionSystem where
  S := pg.Loc × EC
  Act := pg.Act
  I := { ⟨l, η⟩ | (l ∈ pg.Loc0) ∧ }


end ProgramGraph


end Nemonuri

end
