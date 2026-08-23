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
structure State (n k: ℕ) where
  inputs: Vector Bool n
  registers: Vector Bool k
  deriving DecidableEq


namespace State


def vectorEquiv (α: Type _) (n: ℕ) : Vector α n ≃ List.Vector α n where
  toFun v := ⟨v.toList, v.length_toList⟩
  invFun lv := ⟨lv.toArray, lv.property⟩

def vectorProdEquiv (n k: ℕ) : State n k ≃ (List.Vector Bool n × List.Vector Bool k) where
  toFun e := ⟨(vectorEquiv _ _) e.inputs, (vectorEquiv _ _) e.registers⟩
  invFun lv := ⟨(vectorEquiv _ _).symm lv.fst, (vectorEquiv _ _).symm lv.snd⟩

instance toFintype {n k: ℕ} : Fintype (State n k) := Fintype.ofEquiv _ (vectorProdEquiv n k).symm

end State


inductive Act where
  | τ
  deriving DecidableEq, Fintype


inductive AtomicProp (n m k: ℕ) where
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

namespace AtomicProp

/-
def vectorEvalProdEquiv (n m k: ℕ) : AP n m k ≃ (List.Vector Bool m × Eval n k) where
  toFun ap := ⟨(Eval.vectorEquiv _ _) ap.outputs, ⟨ap.inputs, ap.registers⟩⟩
  invFun lve := AP.mk lve.snd.inputs  ((Eval.vectorEquiv _ _).symm lve.fst) lve.snd.registers

instance toFintype {n m k: ℕ} : Fintype (AP n m k) := Fintype.ofEquiv _ (vectorEvalProdEquiv n m k).symm
-/

theorem not_all_zero (ap: AtomicProp 0 0 0) : False := by
  cases ap <;> (
    rename_i i
    rcases i with ⟨i, lm1⟩
    simp at lm1 )

variable {n m k: ℕ}

theorem any_ne_zero (ap: AtomicProp n m k) : (n ≠ 0) ∨ (m ≠ 0) ∨ (k ≠ 0) := by
  by_contra lm1
  simp at lm1
  rcases lm1 with ⟨lm1_1, lm1_2, lm1_3⟩
  subst lm1_1
  subst lm1_2
  subst lm1_3
  exact ap.not_all_zero

theorem nonempty_iff_any_ne_zero : (Nonempty (AtomicProp n m k)) ↔ ((n ≠ 0) ∨ (m ≠ 0) ∨ (k ≠ 0)) := by
  constructor
  · rintro ⟨ap⟩
    exact ap.any_ne_zero
  · intro lm1
    simp only [← Nat.pos_iff_ne_zero] at lm1
    rcases lm1 with lm1 | lm1
    · exact .intro (.inputs (.mk 0 lm1))
    · rcases lm1 with lm1 | lm1
      · exact .intro (.outputs (.mk 0 lm1))
      · exact .intro (.registers (.mk 0 lm1))

def combineBPred (fi: (Fin n) → Bool) (fo: (Fin m) → Bool) (fr: (Fin k) → Bool) (ap: AtomicProp n m k) : Bool :=
  match ap with
  | .inputs i => fi i
  | .registers i => fr i
  | .outputs i => fo i

end AtomicProp


def labeling {n m k: ℕ} (sw: (State n k) → (Fin m) → Bool) (ev: State n k) (ap: AtomicProp n m k) : Bool :=
  match ap with
  | .inputs i => ev.inputs.get i
  | .registers i => ev.registers.get i
  | .outputs i => sw ev i

namespace State

/-
def ofFn {n m k: ℕ} (fn: (AP n m k) → Bool) : Eval n k :=
  let inputs h1 : Vector Bool n := List.finRange n |>.map (fun n' => fn (.inputs n')) |>.toArray |> Vector.mk <| h1
  let registers h2 : Vector Bool k := List.finRange k |>.map (fun n' => fn (.registers n')) |>.toArray |> Vector.mk <| h2
  Eval.mk (inputs (by simp)) (registers (by simp))
-/

def ofFn {n k: ℕ} (fi: (Fin n) → Bool) (fr: (Fin k) → Bool) : State n k := State.mk (.ofFn fi) (.ofFn fr)

/-
theorem ofFn_labeling {n m k: ℕ} (sw: (Eval n k) → (Fin m) → Bool) (fi: (Fin n) → Bool) (fr: (Fin k) → Bool)
  : let fn ev := AP.combineBPred fi (sw ev) fr; labeling sw = fn := by
-/
/-
  refine funext ?_; intro ap
  cases ap <;> rename_i i
  · dsimp [labeling]
    dsimp [ofFn, Vector.get]
    rcases i with ⟨i, lm1⟩
    simp
  · unfold labeling
    dsimp
-/

def ofAPBoolPred {n m k: ℕ} (bpred: AtomicProp n m k → Bool) : State n k :=
  let fi (i: Fin n) := bpred (AtomicProp.inputs i)
  let fr (i: Fin k) := bpred (AtomicProp.registers i)
  State.ofFn fi fr

end State


end SequentialHardwareCircuit


open SequentialHardwareCircuit in
structure SequentialHardwareCircuit (n m k: ℕ) where
  initialRegisters: Vector Bool k
  outputFn : (State n k) → (Fin m) → Bool
  registerFn : (State n k) → (Fin k) → Bool

namespace SequentialHardwareCircuit

variable {n m k: ℕ}

@[mk_iff]
inductive Transition (shcI: SequentialHardwareCircuit n m k) : (State n k) → Act → (State n k) → Prop where
  | intro (s1: State n k) (s2i: Vector Bool n) : Transition shcI s1 .τ (State.mk s2i (Vector.ofFn (shcI.registerFn s1)))

@[reducible]
def toTransitionSystem (shcI: SequentialHardwareCircuit n m k) : TransitionSystem where
  S := State n k
  Act := Act
  I := { s: State n k | s.registers = shcI.initialRegisters }
  AP := AtomicProp n m k
  L := labeling shcI.outputFn
  tr := shcI.Transition

theorem toTransitionSystem_injective : Function.Injective (@toTransitionSystem n m k) := by
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
    specialize lm3 s (AtomicProp.outputs oi)
    dsimp [labeling] at lm3
    exact lm3
  · clear lm2 lm3
    simp only [funext_iff]
    intro s ri
    simp only [funext_iff] at lm1
    specialize lm1 s .τ (State.mk default (Vector.ofFn (rf1 s)))
    simp [transition_iff] at lm1
    rewrite [Vector.ext_iff] at lm1
    simp at lm1
    specialize lm1 ri.val ri.isLt
    simp at lm1
    exact lm1



@[simp]
instance {n m k: ℕ} : TransitionSystemLike (SequentialHardwareCircuit n m k) where
  coe := toTransitionSystem
  coe_injective := toTransitionSystem_injective





section TransitionSystem

open TransitionSystem

variable {n m k: ℕ} {shc: SequentialHardwareCircuit n m k}

instance : ConcreteFinite (shc: TransitionSystem) :=
  .mk inferInstance inferInstance inferInstance


open PropositionalLogics in
theorem labeling_valid (s: State n k)
  : let ts := (shc: TransitionSystem)
    𝐿{ts}⸨s⸩ = (
      (({ xᵢ: Fin n | ts.labeling s (.inputs xᵢ) = .true }: Finset _).image .inputs) ∪
      (({ rᵢ: Fin k | ts.labeling s (.registers rᵢ) = .true }: Finset _).image .registers) ∪
      (({ yᵢ: Fin m | shc.outputFn s yᵢ = .true }: Finset _).image .outputs)
    )
  := by
  extract_lets ts
  simp [Finset.ext_iff]
  dsimp [evalStateToFinset, TransitionSystem.labeling]
  intro ap
  subst ts
  dsimp [Indicator.toFinset] at ap ⊢
  simp
  rcases ap with i | i | i <;> (dsimp [labeling]; simp)


end TransitionSystem
/-
theorem toTransitionSystem_labeling_injective {n m k: ℕ} {shc: SequentialHardwareCircuit n m k} [NeZero m] : Function.Injective ((shc: TransitionSystem).L) := by
  dsimp
  rcases shc with ⟨ir, of, rf⟩
  dsimp
  intro e1 e2 lm2
  simp only [funext_iff] at lm2
  specialize lm2 (AP.outputs (default : Fin m))
  dsimp [labeling] at lm2

open PropositionalLogics Formula
-/

/-
instance {n m k: ℕ} {shc: SequentialHardwareCircuit n m k} : Eval.EvalLike (shc: TransitionSystem).S (shc: TransitionSystem).AP where
  coe e := .mk ((shc: TransitionSystem).L e)
  coe_injective := by
    dsimp
    intro e1 e2
    simp
    intro lm1
    simp only [funext_iff] at lm1
    rcases m with _ | m
    · dsimp [labeling] at lm1
    --have := AP.outputs default
-/

end SequentialHardwareCircuit

end Nemonuri

end
