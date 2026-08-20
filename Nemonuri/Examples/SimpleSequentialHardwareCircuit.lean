module


public import Nemonuri.Executions.Basic

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.11. A Simple Sequential Hardware Circuit, p. 26

-/

@[expose] public section

namespace Examples.SimpleSequentialHardwareCircuit

/-!

### Example 2.11. A Simple Sequential Hardware Circuit

Consider the circuit diagram of the sequential circuit with
1. input variable *x*
2. output variable *y*
3. register *r*

-/

scoped instance : Zero Bool := ⟨.false⟩

@[defeq, scoped simp]
theorem zero_bool : (0: Bool) = .false := rfl

scoped instance : One Bool := ⟨.true⟩

@[defeq, scoped simp]
theorem one_bool : (1: Bool) = .true := rfl

/-- The control function for output variable *y* -/
def «λᵧ» (x: Bool) (r: Bool) : Bool := !(x ^^ r)

/-- The register evaluation changes according to the circuit function -/
def δᵣ (x: Bool) (r: Bool) : Bool := x || r

structure Eval : Type where
  protected x: Bool
  protected r: Bool
  deriving DecidableEq

namespace Eval

def enumList : List Eval := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]

theorem enumList_nodup : enumList.Nodup := by
  dsimp [enumList]
  simp

instance toFintype : Fintype Eval where
  elems := .mk enumList enumList_nodup
  complete := by
    rintro ⟨x, r⟩
    simp
    dsimp [enumList]
    simp
    grind

end Eval

/-- The set of actions is irrelevant and omitted here.
The transitions result directly from the functions λᵧ and δᵣ. -/
inductive Tr : Eval → Unit → Eval → Prop where
  | intro (s: Eval) : Tr s .unit { x := s.x, r := (δᵣ s.x s.r)}

/-- Note that once the register evaluation is [r = 1], r keeps that value. -/
theorem r_keeps_value {s1 s2: Eval} (req1: Tr s1 () s2) (req2: s1.r = 1) : s2.r = 1 := by
  cases req1
  dsimp [δᵣ]
  rw [req2]
  exact Bool.or_true _

inductive AP : Type where
  | protected x
  | protected y
  | protected r
  deriving DecidableEq, Fintype

def labeling (s: Eval) (ap: AP) : Bool :=
  match ap with
  | .x => s.x
  | .r => s.r
  | .y => «λᵧ» s.x s.r

inductive AP' : Type where
  | protected x
  | protected y
  deriving DecidableEq, Fintype

def labeling' (s: Eval) (ap: AP') : Bool :=
  match ap with
  | .x => labeling s .x
  | .y => labeling s .y

open Nemonuri TransitionSystem

@[reducible]
def ts : TransitionSystem where
  S := Eval
  I := { { x := 0, r := 0 }, { x := 1, r := 0 } }
  Act := Unit
  tr := Tr
  AP := AP'
  L := labeling'

instance : ConcreteFinite ts := .mk inferInstance inferInstance inferInstance


example : 𝐿{ts}⸨{ x := 0, r := 0 }⸩ = { .y } := by
  refine Finset.ext ?_; intro ap; dsimp [evalStateToFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton]
  rw [true_and]
  cases lm1: ap <;> dsimp [labeling', labeling]
  · subst lm1
    simp
  · subst lm1
    dsimp [«λᵧ»]
    simp only [iff_true]
    simp only [Bool.bne_false, Bool.not_false]

example : 𝐿{ts}⸨{ x := 0, r := 1 }⸩ = ∅ := by
  refine Finset.ext ?_; intro ap; dsimp [evalStateToFinset]
  simp
  cases lm1: ap <;> dsimp [labeling', labeling]
  · dsimp [«λᵧ»]
    simp

example : 𝐿{ts}⸨{ x := 1, r := 0 }⸩ = { .x } := by
  refine Finset.ext ?_; intro ap; dsimp [evalStateToFinset]
  simp
  cases lm1: ap <;> dsimp [labeling', labeling]
  · simp
  · dsimp [«λᵧ»]; simp

example : 𝐿{ts}⸨{ x := 1, r := 1 }⸩ = { .x, .y } := by
  refine Finset.ext ?_; intro ap; dsimp [evalStateToFinset]
  simp
  cases lm1: ap <;> dsimp [labeling', labeling]
  · simp
  · dsimp [«λᵧ»]; simp

end Examples.SimpleSequentialHardwareCircuit

end
