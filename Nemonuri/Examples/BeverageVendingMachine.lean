
import Nemonuri.TransitionSystem
import Mathlib.Data.FinEnum
import Mathlib.Tactic.DeriveFintype
import Cslib.Foundations.Semantics.LTS.Notation

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.2. Beverage Vending Machine, p.21

-/

namespace Examples

open Nemonuri TransitionSystem

inductive State where
  | pay | select | soda | beer
  deriving DecidableEq

namespace State

def all : List State := [ .pay, .select, .soda, .beer ]

theorem all_mem (x: State) : x ∈ all := by simp [all]; cases x <;> simp

theorem all_nodup : all.Nodup := by
  simp only [all]
  simp only [List.nodup_cons, List.nodup_nil]
  simp only [List.mem_cons, List.mem_nil_iff]
  simp only [reduceCtorEq]
  simp

instance : FinEnum State := FinEnum.ofNodupList all all_mem all_nodup

end State

inductive Act where
  | insert_coin | get_soda | get_beer | τ
  deriving DecidableEq, Fintype

@[lts Tr.toLts "𝑡𝑟"]
inductive Tr : State → Act → State → Prop where
  | pay_select : Tr .pay .insert_coin .select
  | select_soda : Tr .select .τ .soda
  | select_beer : Tr .select .τ .beer
  | soda_pay : Tr .soda .get_soda .pay
  | beer_pay : Tr .beer .get_beer .pay


example : .pay [.insert_coin]⭢𝑡𝑟 .select := Tr.pay_select

example : .beer [.get_beer]⭢𝑡𝑟 .pay := Tr.beer_pay

inductive AP where
  | paid | drink
  deriving DecidableEq, Fintype

set_option trace.Compiler true in
def State.evalToSet (s: State) : Finset AP :=
  match s with
  | .pay => ∅
  | .soda | .beer => { .paid, .drink }
  | .select => { .paid }


def State.eval (s: State) (ap: AP) : Bool := ap ∈ s.evalToSet

@[reducible]
def ts : TransitionSystem where
  S := State
  Act := Act
  tr := Tr
  I := { .pay }
  AP := AP
  L := State.eval

instance : ConcreteFinite ts := .mk inferInstance inferInstance inferInstance


example : 𝐿{ts}⸨.pay⸩ = ∅ := by
  dsimp only [evalStateToFinset, State.eval]; rfl

example : 𝐿{ts}⸨.soda⸩ = { .paid, .drink } := by
  dsimp only [evalStateToFinset, State.eval]; rfl

example : 𝐿{ts}⸨.soda⸩ = 𝐿{ts}⸨.beer⸩ := by
  dsimp only [evalStateToFinset, State.eval]; rfl

example : 𝐿{ts}⸨.select⸩ = { .paid } := by
  dsimp only [evalStateToFinset, State.eval]; rfl




end Examples
