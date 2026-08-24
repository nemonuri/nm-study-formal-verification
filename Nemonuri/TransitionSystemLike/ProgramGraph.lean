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


@[reducible]
def toIndicatorLike
  [Fintype Var] [Fintype Val] [DecidableEq Val] (sty: StandardType EC Var Val) [sty.DecidableSafe] (req: Function.Injective (sty.indicateAtomicProp))
  : PropositionalLogics.EvalLike EC (sty.AtomicProp) where
  coe ec := sty.indicateAtomicProp ec |> .mk
  coe_injective := by
    intro _ _
    simp
    exact req.eq_iff.mp

section Cond

variable [Fintype Var] [Fintype Val] [DecidableEq Val]

open PropositionalLogics

inductive IsCond (sty: StandardType EC Var Val) [sty.DecidableSafe] : Formula sty.AtomicProp → Prop where
  | nil : IsCond sty (.true)
  | cons (ap: sty.AtomicProp) (fml: Formula sty.AtomicProp) : IsCond sty (Formula.and (.atom ap) fml)

attribute [simp] IsCond.nil

end Cond

end StandardType


open PropositionalLogics in
structure Cond (EC Var Val: Type*) [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] (sty: StandardType EC Var Val) [sty.DecidableSafe] where
  formula: Formula sty.AtomicProp
  valid : sty.IsCond formula


class CondLike (CC EC Var Val: Type*) [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] where
  standardType: StandardType EC Var Val
  [decidableSafe: standardType.DecidableSafe]
  toCond: CC → Cond EC Var Val standardType
  toCond_Injective: Function.Injective toCond

attribute [implicit_reducible, instance] CondLike.decidableSafe

end ProgramGraph

/-!

### Definition 2.13. Program Graph (PG)

-/


open ProgramGraph in
structure ProgramGraph (CC EC Var Val: Type*) [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] [CondLike CC EC Var Val] where
  Loc: Type*
  [decidableEqOfLoc: DecidableEq Loc]
  Act: Type*
  effect: Act → EC → EC
  ctr: Loc → CC → Act → Loc → Prop
  loc0: Loc → Prop
  g0: Cond EC Var Val (CondLike.standardType CC)


/-!

### Definition 2.15. Transition System Semantics of a Program Graph

-/

namespace ProgramGraph

variable {CC EC Var Val: Type*} [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] [cl: CondLike CC EC Var Val]

instance (pg: ProgramGraph CC EC Var Val) : DecidableEq (pg.Loc) := pg.decidableEqOfLoc

def Loc0 (pg: ProgramGraph CC EC Var Val) : Set (pg.Loc) := { l | pg.loc0 l }

inductive Transition (pg: ProgramGraph CC EC Var Val) (req: Function.Injective ((cl.standardType).indicateAtomicProp)) : (pg.Loc × EC) → pg.Act → (pg.Loc × EC) → Prop where
  | intro (l1 l2: pg.Loc) (g: CC) (act: pg.Act) (η: EC) (req1: pg.ctr l1 g act l2)
          (req2: η ⊨ₚ{ EC , (cl.standardType).AtomicProp , _ , (cl.standardType).toIndicatorLike req } (cl.toCond g).formula)
      : Transition pg req ⟨l1, η⟩ act ⟨l2, pg.effect act η⟩

open PropositionalLogics in
def labeling (pg: ProgramGraph CC EC Var Val) (s: pg.Loc × EC) (ap: pg.Loc ⊕ CC) : Bool :=
  let ⟨l, η⟩ := s
  match ap with
  | .inl l2 => decide (l = l2)
  | .inr g => (Indicator.mk (cl.standardType.indicateAtomicProp η)).evalFormulaToBool (cl.toCond g).formula


open PropositionalLogics in
@[reducible]
def toTransitionSystem (pg: ProgramGraph CC EC Var Val) (req: Function.Injective ((cl.standardType).indicateAtomicProp)) : TransitionSystem :=
  let ind := (cl.standardType).toIndicatorLike req
  let Cap := (cl.standardType).AtomicProp
  {
    S := pg.Loc × EC
    Act := pg.Act
    I := { ⟨l, η⟩ | (l ∈ pg.Loc0) ∧ (η ⊨ₚ{ EC , Cap , _ , ind } pg.g0.formula) }
    AP := pg.Loc ⊕ CC
    tr := pg.Transition req
    L := pg.labeling
  }

#print toTransitionSystem

--/-(η ⊨ₚ{ @SatRel.defaultAt EC (cl.standardType).AtomicProp (inferInstance: Fintype (cl.standardType).AtomicProp) ((cl.standardType).toIndicatorLike req) } pg.g0 )-/

end ProgramGraph


end Nemonuri

end
