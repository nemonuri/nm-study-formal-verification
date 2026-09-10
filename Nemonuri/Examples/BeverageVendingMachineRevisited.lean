module

public import Nemonuri.TransitionSystemLike.ProgramGraph
public import Nemonuri.Examples.BeverageVendingMachine
public import Nemonuri.PropositionalLogics.Tactic
public import Mathlib.Data.Fintype.Powerset

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

open ProgramGraph.StandardType

protected def standardType : ValueSetSafeDecidable State Var Val (Finset Val) where
  dom _ := Finset.univ
  isValueSetSafe _ _ := .true
  valid := by
    refine ⟨⟨?_, ?_, ⟩, ?_⟩
    · simp
    · simp
      intro var val
      rcases var
      · let w: State := .mk val.val 0
        exists w
      · let w: State := .mk 0 val.val
        exists w
    · simp
      dsimp [ProgramGraph.StandardTypeStruct.isValueSetSafe_def]
      simp


instance : HasSafeDecidable State Var Val (Finset Val) where
  standardType := Revisited.standardType
  decidableMem _ := inferInstance

open HasSafeDecidable in
theorem standardType_is_always_safe {var: Var} {val: Val} : (standardTypeAt State (Finset Val)).IsValueSafe var val := by
  dsimp [standardTypeAt_def, HasSafeDecidable.standardType, ProgramGraph.StandardTypeStruct.isValueSafe_def, Revisited.standardType]
  simp

theorem is_atomic_prop {s: AtomicPropStruct Var (Finset Val)} : IsAtomicProp s State Val := by
  rw [isAtomicProp_iff_forall_spec_elem_value_safe]
  simp [standardType_is_always_safe]

protected def singletonOP : AtomicProp.SingletonOP State Var Val (Finset Val) where
  op var val _ := ⟨⟨var, {val}⟩, is_atomic_prop⟩
  valid := by
    refine .mk ?_ ?_
    · simp
    · simp


instance : AtomicProp.HasSingletonOP State Var Val (Finset Val) where
  singletonOP := Revisited.singletonOP


instance : HasProposition State Var Val where
  ValS := Finset Val
  setLike := inferInstance
  hasSafeDecidable := inferInstance
  hasSingletonOP := inferInstance
  fintypeVar := inferInstance
  fintypeSpec := Finset.fintype


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

--attribute [local simp] standardType StandardType.isSafe_iff in
open HasProposition in
def toFormula (g: Guard) : ProgramGraph.Cond State Var Val :=
  match g with
  | .true => .ofAtoms []
  | .nsoda_gt_zero => .ofAtoms [⟨⟨.nsoda, Finset.univ.filter (fun val => val.val.val > 0)⟩, is_atomic_prop⟩]
  | .nbeer_gt_zero => .ofAtoms [⟨⟨.nbeer, Finset.univ.filter (fun val => val.val.val > 0)⟩, is_atomic_prop⟩]
  | .nsoda_eq_zero_and_nbeer_eq_zero =>
    let ap1 : AtomicPropType State Var Val := ⟨⟨.nsoda, Finset.univ.filter (fun val => val.val.val = 0)⟩, is_atomic_prop⟩
    let ap2 : AtomicPropType State Var Val := ⟨⟨.nbeer, Finset.univ.filter (fun val => val.val.val = 0)⟩, is_atomic_prop⟩
    .ofAtoms [ap1, ap2]


theorem toFormula_injective : Function.Injective toFormula := by
  intro g1 g2 lm1
  cases g1 <;> cases g2 <;> simp <;> simp [toFormula, Cond.ofAtoms_injective.eq_iff] at lm1



instance : ProgramGraph.CondLike Guard State Var Val where
  toCond := toFormula
  toCond_Injective := toFormula_injective


def initial : ProgramGraph.Cond State Var Val := .ofAtoms [⟨⟨.nsoda, Finset.univ.filter (fun val => val.val.val = 2)⟩, is_atomic_prop⟩]

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
theorem example1 : transitionSystem.tr (Loc.start, State.mk 2 2) Act.refill (Loc.start, State.mk 2 2) := by
  dsimp [transitionSystem]
  refine .intro _ _ Guard.true _ _ ?_ ?_
  · dsimp
    exact .refill
  · dsimp [ProgramGraph.CondLike.toFormula, ProgramGraph.CondLike.toCond, Guard.toFormula, ProgramGraph.Cond.ofAtoms]
    simp [pl_simp]


open PropositionalLogics in
theorem example2 : transitionSystem.tr (Loc.select, State.mk 1 2) Act.sget (Loc.start, State.mk 0 2) := by
  dsimp [transitionSystem]
  refine ProgramGraph.Transition.of_exists ?_
  simp
  exists Guard.nsoda_gt_zero
  refine ⟨?_, ?_⟩
  · exact .sget
  · dsimp [ProgramGraph.CondLike.toFormula, ProgramGraph.CondLike.toCond, Guard.toFormula, ProgramGraph.Cond.ofAtoms]
    simp [pl_simp]
    dsimp [EvalLike.coe, DFunLike.coe, AtomicPropStruct.decideEvalSpecSafe]
    simp
    dsimp [AtomicPropStruct.isEvalSpecSafe_def, DFunLike.coe, State.eval]
    rw [Finset.mem_def]
    simp


end Examples.BeverageVendingMachines.Revisited

end
