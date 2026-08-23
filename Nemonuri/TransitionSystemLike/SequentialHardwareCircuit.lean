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

#check Eq.refl
#check HEq.subst

/-
theorem _root_.Vector.size_eq_of_heq {α: Type _} {n1 n2: ℕ} {v1: Vector α n1} {v2: Vector α n2} (req: v1 ≍ v2)
  : n1 = n2 := by
  let Spec (T: Type _) (x: T) : Prop := ∃(n: ℕ), ∃(h: T = Vector α n), ((cast h x).size = n1 ∧ n ≠ n2)
  have lm2 : Spec _ v1 := by
    simp [Spec]
    exists n1
    simp
    exact lm1
  have lm3 := req.subst lm2
  subst Spec
  simp at lm3
  obtain ⟨n, ⟨lm3_1, lm3_2⟩, lm4⟩ := lm3
  dsimp [Vector.size] at lm3_2
-/





/-
  let Spec (T: Type _) (x: T) : Prop := ∃!(n: ℕ), ∃(h: T = Vector α n), ((cast h x).size = n1)
  have lm1 : Spec _ v1 := by
    simp [Spec, ExistsUnique]
    exists n1
    constructor
    · exists rfl
    · intro n lm1 lm2
      dsimp [Vector.size] at lm2
      exact lm2
  have lm2 := req.subst lm1
  subst Spec
  simp [ExistsUnique] at lm2
  obtain ⟨n, ⟨lm2_1, lm2_2⟩, lm3⟩ := lm2
  have lm4 := lm3 n2 rfl
  dsimp [Vector.size] at lm4
  have lm5 := type_eq_of_heq req
  have lm6 := lm3 n1 lm5.symm
  dsimp [Vector.size] at lm6
  simp at lm6
-/
  --simp [ExistsUnique] at lm1


/-
  have lm1 := Eq.refl v2.size
  conv at lm1 => rhs; dsimp [Vector.size]
  have lm2 : v1.size = n2 := @req.subst
-/

  --by_contra lm1
  --obtain ⟨lm4, lm5⟩ := heq_iff_exists_cast_eq.mp req.symm
  --have lm3 := congrArg (Vector.size) lm2
  --dsimp [Vector.size] at lm3
  --rewrite [Vector.ext_iff] at lm2
  --rewrite [heq_iff_exists_cast_eq] at req

  --have lm1 := type_eq_of_heq req
  --have := req.
  --have := Vector.ext
/-
  rcases v1 with ⟨⟨l1⟩, lm1⟩
  rcases v2 with ⟨⟨l2⟩, lm2⟩
  revert lm1 lm2
  simp
  intro lm1 lm2 req
-/
  --have lm3 := type_eq_of_heq req


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

structure Indexed (n m k: ℕ) where
  initialRegisters: Vector Bool k
  outputFn : (State n k) → (Fin m) → Bool
  registerFn : (State n k) → (Fin k) → Bool

namespace Indexed

variable {n m k: ℕ}

@[mk_iff]
inductive Transition (shcI: Indexed n m k) : (State n k) → Act → (State n k) → Prop where
  | intro (s1: State n k) (s2i: Vector Bool n) : Transition shcI s1 .τ (State.mk s2i (Vector.ofFn (shcI.registerFn s1)))

@[reducible]
def toTransitionSystem (shcI: Indexed n m k) : TransitionSystem where
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

end Indexed

end SequentialHardwareCircuit


open SequentialHardwareCircuit in
structure SequentialHardwareCircuit where --(n m k: ℕ)
  inputLength : ℕ
  registerLength : ℕ
  outputLength : ℕ
  indexed : Indexed inputLength registerLength outputLength
  --initialRegisters: Vector Bool registerLength
  --outputFn : (State inputLength registerLength) → (Fin outputLength) → Bool
  --registerFn : (State inputLength registerLength) → (Fin registerLength) → Bool


namespace SequentialHardwareCircuit

#check type_eq_of_heq

@[reducible]
def toTransitionSystem (shc: SequentialHardwareCircuit) : TransitionSystem := shc.indexed.toTransitionSystem


/-
theorem toTransitionSystem_injective : Function.Injective (toTransitionSystem) := by
  intro shc1 shc2 lm1
  dsimp [toTransitionSystem] at lm1
  dsimp [Indexed.toTransitionSystem] at lm1
  simp at lm1
  revert lm1
  simp
  intro lm1 lm2 lm3 lm4 lm5
  have lm6 := type_eq_of_heq lm2
-/
  --have lm2 := Indexed.toTransitionSystem_injective.eq_iff.mp lm1
  --have lm2 := fun n m k => @Indexed.toTransitionSystem_injective n m k
  --dsimp [Function.Injective] at lm2
  --dsimp [Indexed.toTransitionSystem] at lm1
/-
  rcases shc1 with ⟨n1, m1, k1, shcI1⟩
  rcases shc2 with ⟨n2, m2, k2, shcI2⟩
  simp at lm1 ⊢
-/


--def toLabeling {n m k: ℕ} (shc: SequentialHardwareCircuit n m k) (s: Eval n k) (ap: Subtype (shc.apFilter · = .true)) : Bool := labeling shc.outputFn s ap.val

/-
@[mk_iff]
inductive Transition (shc: SequentialHardwareCircuit) : (State shc.inputLength shc.registerLength) → Act → (State shc.inputLength shc.registerLength) → Prop where
  | intro (s1: State shc.inputLength shc.registerLength) (s2i: Vector Bool shc.inputLength) : Transition shc s1 .τ (State.mk s2i (Vector.ofFn (shc.registerFn s1)))


@[reducible]
def toTransitionSystem (shc: SequentialHardwareCircuit) : TransitionSystem where
  S := State shc.inputLength shc.registerLength
  Act := Act
  I := { s: State shc.inputLength shc.registerLength | s.registers = shc.initialRegisters }
  AP := AtomicProp shc.inputLength shc.outputLength shc.registerLength
  L := labeling shc.outputFn
  tr := shc.Transition


theorem toTransitionSystem_injective : Function.Injective (toTransitionSystem) := by
  --rintro ⟨n1, m1, k1, ir1, of1, rf1⟩ ⟨n2, m2, k2, ir2, of2, rf2⟩
  intro shc1 shc2
  simp [toTransitionSystem]
  intro lm1 lm2 lm3 lm4 lm5
  rewrite [heq_iff_exists_cast_eq] at lm3
  rcases lm3 with ⟨lm6, lm3⟩
  rewrite [Set.ext_iff] at lm3
  simp at lm3
  let st1 : State shc2.inputLength shc2.registerLength := .mk default shc2.initialRegisters
  specialize lm3 st1
  subst st1
  simp at lm3
  dsimp [cast] at lm3
/-
  rewrite [heq_iff_exists_cast_eq] at lm2
  rcases lm2 with ⟨lm6, lm2⟩
  simp only [funext_iff] at lm2
  simp at lm2
-/
/-

  rcases ir1 with ⟨⟨ir1_l⟩, ir1_s⟩
  rcases ir2 with ⟨⟨ir2_l⟩, ir2_s⟩
  revert lm2 lm3 ir1_s ir2_s
  simp
  intro ir1_s ir2_s lm2 lm3
  unfold labeling at lm5
-/


  --rintro ⟨n1, m1, k1, ir1, of1, rf1⟩ ⟨n2, m2, k2, ir2, of2, rf2⟩

  --intro lm1 lm2 lm3 lm4 lm5
/-


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
-/

@[simp]
instance {n m k: ℕ} : TransitionSystemLike (SequentialHardwareCircuit n m k) where
  coe := toTransitionSystem
  coe_injective := toTransitionSystem_injective





section TransitionSystem

open TransitionSystem

variable {n m k: ℕ} {shc: SequentialHardwareCircuit n m k}

instance : ConcreteFinite (shc: TransitionSystem) :=
  .mk inferInstance inferInstance inferInstance

--instance : Fintype ((shc: TransitionSystem).AP) := inferInstance

/-
--set_option trace.Meta.synthInstance true in
open PropositionalLogics in
theorem labeling_valid (s: Eval n k)
  : let ts := (shc: TransitionSystem)
    --let : EvalLike (Quotient ts.toLabelingSetoid) (AP n m k) := inferInstanceAs (EvalLike (Quotient ts.toLabelingSetoid) ts.AP)
    𝐿{ts}⸨s⸩ = (
      (Finset.image AP.inputs { xᵢ: Fin n | ts.labeling s (.inputs xᵢ) = .true }) ∪
      (Finset.image AP.registers { rᵢ: Fin k | ts.labeling s (.registers rᵢ) = .true }) ∪
      (Finset.image AP.outputs { yᵢ: Fin m | shc.outputFn s yᵢ = .true  })
    )
  := by
  extract_lets ts
  simp [Finset.ext_iff]
  dsimp [evalStateToFinset, TransitionSystem.labeling]
  intro ap
  subst ts
  dsimp at ap ⊢
  --revert ap
  --simp --[TransitionSystemLike.coe]
-/

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
-/
end SequentialHardwareCircuit

end Nemonuri

end
