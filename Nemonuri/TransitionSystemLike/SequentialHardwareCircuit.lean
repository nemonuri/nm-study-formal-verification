module

public import Nemonuri.TransitionSystemLike.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Sum

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.11. A Simple Sequential Hardware Circuit, p. 28

-/

@[expose] public section

namespace Nemonuri

namespace SequentialHardwareCircuit

/-- *n* input bits, *m* output bits, *k* registers -/
structure Eval (n k: ℕ) where
  inputs: Vector Bool n
  registers: Vector Bool k
  deriving DecidableEq

namespace Eval


def vectorEquiv (α: Type _) (n: ℕ) : Vector α n ≃ List.Vector α n where
  toFun v := ⟨v.toList, v.length_toList⟩
  invFun lv := ⟨lv.toArray, lv.property⟩

def vectorProdEquiv (n k: ℕ) : Eval n k ≃ (List.Vector Bool n × List.Vector Bool k) where
  toFun e := ⟨(vectorEquiv _ _) e.inputs, (vectorEquiv _ _) e.registers⟩
  invFun lv := ⟨(vectorEquiv _ _).symm lv.fst, (vectorEquiv _ _).symm lv.snd⟩

instance toFintype {n k: ℕ} : Fintype (Eval n k) := Fintype.ofEquiv _ (vectorProdEquiv n k).symm

end Eval


inductive Act where
  | τ
  deriving DecidableEq, Fintype


inductive AP (n m k: ℕ) where
  | inputs (i: Fin n)
  | outputs (i: Fin m)
  | registers (i: Fin k)
  deriving DecidableEq, Fintype

/-
  inputs: Vector Bool n
  outputs: Vector Bool m
  registers: Vector Bool k
  deriving DecidableEq
-/

namespace AP

/-
def vectorEvalProdEquiv (n m k: ℕ) : AP n m k ≃ (List.Vector Bool m × Eval n k) where
  toFun ap := ⟨(Eval.vectorEquiv _ _) ap.outputs, ⟨ap.inputs, ap.registers⟩⟩
  invFun lve := AP.mk lve.snd.inputs  ((Eval.vectorEquiv _ _).symm lve.fst) lve.snd.registers

instance toFintype {n m k: ℕ} : Fintype (AP n m k) := Fintype.ofEquiv _ (vectorEvalProdEquiv n m k).symm
-/

end AP


def labeling {n m k: ℕ} (sw: (Eval n k) → (Fin m) → Bool) (ev: Eval n k) (ap: AP n m k) : Bool :=
  match ap with
  | .inputs i => ev.inputs.get i
  | .registers i => ev.registers.get i
  | .outputs i => sw ev i


end SequentialHardwareCircuit

open SequentialHardwareCircuit in
structure SequentialHardwareCircuit (n m k: ℕ) where
  initialRegisters: Vector Bool k
  --apFilter : (AP n m k) → Bool
  outputFn : (Eval n k) → (Fin m) → Bool
  registerFn : (Eval n k) → (Fin k) → Bool

namespace SequentialHardwareCircuit

--def toLabeling {n m k: ℕ} (shc: SequentialHardwareCircuit n m k) (s: Eval n k) (ap: Subtype (shc.apFilter · = .true)) : Bool := labeling shc.outputFn s ap.val

@[mk_iff]
inductive Transition {n m k: ℕ} (shc: SequentialHardwareCircuit n m k) : (Eval n k) → Act → (Eval n k) → Prop where
  | intro (s1: Eval n k) (s2i: Vector Bool n) : Transition shc s1 .τ (Eval.mk s2i (Vector.ofFn (shc.registerFn s1)))


@[reducible]
def toTransitionSystem {n m k: ℕ} (shc: SequentialHardwareCircuit n m k) : TransitionSystem where
  S := Eval n k
  Act := Act
  I := { e: Eval n k | e.registers = shc.initialRegisters }
  AP := AP n m k
  L := labeling shc.outputFn
  tr := shc.Transition


theorem toTransitionSystem_injective {n m k: ℕ} : Function.Injective (@toTransitionSystem n m k) := by
  rintro ⟨ir1, of1, rf1⟩ ⟨ir2, of2, rf2⟩
  simp [toTransitionSystem]
  intro lm1 lm2 lm3
  refine ⟨?_, ?_, ?_⟩
  · clear lm1 lm3
    simp [Set.ext_iff] at lm2
    have lm2_1 := lm2 ⟨default, ir1⟩
    simp at lm2_1
    exact lm2_1
  · clear lm1 lm2
    simp only [funext_iff]
    intro s oi
    simp only [funext_iff] at lm3
    specialize lm3 s (AP.outputs oi)
    dsimp [labeling] at lm3
    exact lm3
  · clear lm2 lm3
    simp only [funext_iff]
    intro s ri
    simp only [funext_iff] at lm1
    specialize lm1 s .τ (Eval.mk default (Vector.ofFn (rf1 s)))
    simp [transition_iff] at lm1
    rewrite [Vector.ext_iff] at lm1
    simp at lm1
    specialize lm1 ri.val ri.isLt
    simp at lm1
    exact lm1


instance {n m k: ℕ} : TransitionSystemLike (SequentialHardwareCircuit n m k) where
  coe := toTransitionSystem
  coe_injective := toTransitionSystem_injective


end SequentialHardwareCircuit

end Nemonuri

end
