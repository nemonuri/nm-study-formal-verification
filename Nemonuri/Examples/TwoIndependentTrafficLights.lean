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

variable {AP: Type _} [DecidableEq AP] (lb1 lb2: State → AP → Bool)

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

def areRelOfAct : Act1 → Act2 → Bool
  | .a, .c | .b, .d => .true
  | _, _ => .false

theorem areRelOfAct_biUnique : Relator.BiUnique (areRelOfAct · · = .true) := by
  dsimp [Relator.BiUnique]
  refine ⟨?_, ?_⟩
  · intro a1_1 a1_2 a2
    rcases a1_1 <;> rcases a1_2 <;> rcases a2 <;> simp [areRelOfAct]
  · intro a1 a2_1 a2_2
    rcases a1 <;> rcases a2_1 <;> rcases a2_2 <;> simp [areRelOfAct]

def interleaving : TransitionSystem.Interleaving (trLight1 lb1) (trLight2 lb2) where
  act := .mk areRelOfAct areRelOfAct_biUnique
  ap := .refl AP

open Relations.Heterogeneous

instance : HasPartialCongruence (interleaving lb1 lb2).ap.Rel := ⟨PartialCongruence.ofBiUniqueIndicatorRefl AP⟩


theorem example1 : (interleaving lb1 lb2).toTransitionSystem.tr (.red, .red) (.ofSum (.inl .a)) (.green, .red) := by
  dsimp
  refine .fst _ _ _ ?_ _
  dsimp
  exact .a

theorem example2 : (interleaving lb1 lb2).toTransitionSystem.tr (.red, .green) (.ofSum (.inr .d)) (.red, .red) := by
  dsimp
  refine .snd _ _ _ ?_ _
  dsimp
  exact .d

/-
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
-/

end Examples.TrafficLights.TwoIndependent

end
