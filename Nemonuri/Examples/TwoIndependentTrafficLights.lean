module

public import Nemonuri.TransitionSystemLike.Interleaving
public import Mathlib.Tactic.DeriveFintype

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.17. Two Independent Traffic Lights, p. 36

-/

@[expose] public section

namespace Examples.TrafficLights.TwoIndependent

inductive State where
  | red
  | green
  deriving DecidableEq, Fintype

inductive Act1 where
  | a
  | b
  deriving DecidableEq, Fintype

inductive Act2 where
  | c
  | d
  deriving DecidableEq, Fintype

variable {AP: Type _} (lb1 lb2: State → AP → Bool)

open Nemonuri

inductive Transition1 : State → Act1 → State → Prop where
  | a : Transition1 .red .a .green
  | b : Transition1 .green .b .red

inductive Transition2 : State → Act2 → State → Prop where
  | c : Transition2 .red .c .green
  | d : Transition2 .green .d .red

@[reducible]
def trLight1 : TransitionSystem where
  S := State
  Act := Act1
  tr := Transition1
  I := {.red}
  AP := AP
  L := lb1

@[reducible]
def trLight2 : TransitionSystem where
  S := State
  Act := Act2
  tr := Transition2
  I := {.red}
  AP := AP
  L := lb2


def interleaving : TransitionSystem.Interleaving (Act1 ⊕ Act2) AP (trLight1 lb1) (trLight2 lb2) where
  actHasHUnionBundle := HasHUnion.Bundle.ofSum Act1 Act2
  apHasHUnionBundle := HasHUnion.Bundle.ofRefl AP

open Nemonuri.HasHUnion in
theorem example1 : (interleaving lb1 lb2).toTransitionSystem.tr (.red, .red) ⟨Sum.inl .a, by simp [hunionSetUnivAt_mem_iff]; left; exists .a⟩ (.green, .red) := by
  simp [interleaving]
  refine .fst _ _ _ ?_ _
  dsimp
  exact .a

open Nemonuri.HasHUnion in
theorem example2 : (interleaving lb1 lb2).toTransitionSystem.tr (.red, .green) ⟨Sum.inr .d, by simp [hunionSetUnivAt_mem_iff]; right; exists .d⟩ (.red, .red) := by
  simp [interleaving]
  refine .snd _ _ _ ?_ _
  dsimp
  exact .d

end Examples.TrafficLights.TwoIndependent

end
