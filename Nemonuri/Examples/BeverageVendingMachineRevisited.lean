module

public import Nemonuri.TransitionSystemLike.ProgramGraph
public import Nemonuri.Examples.BeverageVendingMachine

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




end Guard

/-
instance : ProgramGraph.CondLike Guard State Var Val where
  standardType := standardType
  toCond
-/
end Examples.BeverageVendingMachines.Revisited

end
