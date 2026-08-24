module

public import Nemonuri.TransitionSystemLike.ProgramGraph
public import Nemonuri.Examples.BeverageVendingMachine
public import Nemonuri.PropositionalLogics.Tactic

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.12. Beverage Vending Machine Revisited, p. 29

-/

@[expose] public section

namespace Examples.BeverageVendingMachines.Revisited

open Nemonuri

inductive Act where
  | coin | refill | sget | bget | ret_coin
  deriving DecidableEq, Fintype

inductive Loc where
  | start | select
  deriving DecidableEq, Fintype

inductive Var where
  | nsoda
  | nbeer
  deriving DecidableEq, Fintype

structure Val where
  val: Fin 3
  deriving DecidableEq, Fintype

structure State where
  nsoda : Fin 3
  nbeer : Fin 3

def State.eval (s: State) (var: Var) : Val :=
  match var with
  | .nsoda => s.nsoda |> .mk
  | .nbeer => s.nbeer |> .mk

@[simp]
instance : ProgramGraph.EvalLike State Var Val where
  coe s := .mk (s.eval)
  coe_injective := by
    rintro ⟨_,_⟩ ⟨_,_⟩
    simp [funext_iff]
    intro lm1
    dsimp [State.eval] at lm1
    have lm2 := lm1 .nsoda
    have lm3 := lm1 .nbeer
    simp at lm2 lm3
    simp [lm2, lm3]

def standardType : ProgramGraph.StandardType State Var Val where
  dom _ := Set.univ
  valid := by simp

theorem standardType_is_always_safe (var: Var) (dom: Set Val) (val: Val) (_: val ∈ dom) : val ∈ standardType.dom var := by
  dsimp [standardType]
  simp

instance : standardType.DecidableSafe := fun v d => decidable_of_iff True (by simp [ProgramGraph.StandardType.isSafe_iff]; exact standardType_is_always_safe v d)

inductive Guard where
  | true
  | nsoda_gt_zero
  | nbeer_gt_zero
  | nsoda_eq_zero_and_nbeer_eq_zero
  deriving DecidableEq, Fintype

namespace Guard

open PropositionalLogics
open ProgramGraph

instance : Inhabited Var := ⟨.nsoda⟩

attribute [local simp] standardType StandardType.isSafe_iff in
def toFormula (g: Guard) : ProgramGraph.Cond State Var Val standardType  :=
  match g with
  | .true => .ofAtoms []
  | .nsoda_gt_zero => .ofAtoms [⟨.nsoda, fun val => val.val.val > 0, by simp⟩]
  | .nbeer_gt_zero => .ofAtoms [⟨.nbeer, fun val => val.val.val > 0, by simp⟩]
  | .nsoda_eq_zero_and_nbeer_eq_zero =>
    let ap1 : standardType.AtomicProp := ⟨.nsoda, fun val => val.val.val = 0, by simp⟩
    let ap2 : standardType.AtomicProp := ⟨.nbeer, fun val => val.val.val = 0, by simp⟩
    .ofAtoms [ap1, ap2]


theorem toFormula_injective : Function.Injective toFormula := by
  intro g1 g2 lm1
  cases g1 <;> cases g2 <;> simp <;> simp [toFormula, Cond.ofAtoms_eq_iff_eq] at lm1


instance : ProgramGraph.CondLike Guard State Var Val where
  standardType := standardType
  toCond := toFormula
  toCond_Injective := toFormula_injective


def initial : ProgramGraph.Cond State Var Val standardType := .ofAtoms [⟨.nsoda, fun val => val.val.val = 2, by simp [standardType, StandardType.isSafe_iff]⟩]

end Guard

def effect (act: Act) (st1: State) : State :=
  match act with
  | .coin | .ret_coin => st1
  | .refill => .mk 2 2
  | .sget => { st1 with nsoda := st1.nsoda - 1 }
  | .bget => { st1 with nbeer := st1.nbeer - 1 }


inductive Ctr : Loc → Guard → Act → Loc → Prop where
  | coin : Ctr .start .true .coin .select
  | refill : Ctr .start .true .refill .start
  | sget : Ctr .select .nsoda_gt_zero .sget .start
  | bget : Ctr .select .nbeer_gt_zero .bget .start
  | ret_coin : Ctr .select .nsoda_eq_zero_and_nbeer_eq_zero .ret_coin .start


@[reducible]
def programGraph : ProgramGraph Guard State Var Val where
  Loc := Loc
  Act := Act
  effect := effect
  g0 := Guard.initial
  loc0 := fun l => l = .start
  ctr := Ctr

@[reducible]
def transitionSystem : TransitionSystem := programGraph.toTransitionSystem

open PropositionalLogics in
example : transitionSystem.tr (Loc.start, State.mk 2 2) Act.refill (Loc.start, State.mk 2 2) := by
  dsimp [transitionSystem]
  refine .intro _ _ Guard.true _ _ ?_ ?_
  · dsimp
    exact .refill
  · dsimp [ProgramGraph.CondLike.toCond, Guard.toFormula, ProgramGraph.Cond.ofAtoms, Formula.atomTuple, Formula.iterAnd]
    simp [pl_simp]
/-
    dsimp [ProgramGraph.CondLike.standardType, ProgramGraph.CondLike.toCond,
           SatRel.IsSat, SatRel.defaultAt, Inhabited.default, SatRel.default, DFunLike.coe,
           EvalLike.toIndicator, EvalLike.coe]
    simp only [← Indicator.AreEvalToTrue.eq_true_iff]
    dsimp [Guard.toFormula]
    dsimp [Indicator.evalFormulaToBool]
-/

open PropositionalLogics in
example : transitionSystem.tr (Loc.select, State.mk 1 2) Act.sget (Loc.start, State.mk 0 2) := by
  dsimp [transitionSystem]
  rw [ProgramGraph.transition_iff]
  simp
  exists Guard.nsoda_gt_zero
  refine ⟨?_, ?_, ?_⟩
  · exact .sget
  · dsimp [ProgramGraph.CondLike.toCond, Guard.toFormula, ProgramGraph.Cond.ofAtoms, Formula.atomTuple, Formula.iterAnd]
    simp [pl_simp]
    dsimp [EvalLike.coe]
    dsimp [ProgramGraph.StandardType.indicateAtomicProp, ProgramGraph.EvalLike.coe, DFunLike.coe]
    dsimp [State.eval]
    simp
/-
    dsimp [ProgramGraph.CondLike.standardType, ProgramGraph.CondLike.toCond,
           SatRel.IsSat, SatRel.defaultAt, Inhabited.default, SatRel.default, DFunLike.coe,
           EvalLike.toIndicator, EvalLike.coe]
    simp only [← Indicator.AreEvalToTrue.eq_true_iff]
    dsimp [Guard.toFormula]
    dsimp [Indicator.evalFormulaToBool, Indicator.fn]
    simp
    dsimp [ProgramGraph.StandardType.indicateAtomicProp, ProgramGraph.EvalLike.coe, DFunLike.coe, Indicator.mk]
    dsimp [State.eval]
    simp
-/
  · dsimp [effect]





end Examples.BeverageVendingMachines.Revisited

end
