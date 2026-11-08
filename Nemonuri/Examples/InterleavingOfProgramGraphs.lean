module

public meta import Mathlib.Tactic.DeriveFintype
public import Nemonuri.TransitionSystemLike.ProgramGraph.Interleaving
public import Mathlib.Data.Fintype.Powerset


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.22. Interleaving of Program Graphs, p.40

-/

@[expose] public section

set_option autoImplicit false

namespace Examples.InterleavingOfProgramGraphs

open Nemonuri ProgramGraph

inductive Loc1 where
  | pre
  | post
  deriving DecidableEq, Fintype

inductive Loc2 where
  | pre
  | post
  deriving DecidableEq, Fintype

inductive Act1 where
  | act
  deriving DecidableEq, Fintype

inductive Act2 where
  | act
  deriving DecidableEq, Fintype

inductive Var where
  | x
  deriving DecidableEq, Fintype

structure State where
  x : Int32

instance : EvalLike State Var Int32 where
  coe st := ⟨fun _ => st.x⟩
  coe_injective := by
    rintro ⟨_⟩ ⟨_⟩
    simp [funext_iff]
    intro lm1
    exact lm1 .x


namespace State

def updateOp : EvalLike.UpdateOP State Var Int32 where
  op _ val st := { st with x := val }
  valid := by
    refine .mk ?_
    dsimp
    intro _ _ ⟨_⟩
    simp [funext_iff]
    intro _
    rfl


end State


def int32EquivToFin : Int32 ≃ Fin (2 ^ 32) where
  toFun i := i.toBitVec.toFin
  invFun fin := Int32.ofBitVec (BitVec.ofFin fin)

scoped instance : Fintype Int32 := Fintype.ofEquiv (Fin (2 ^ 32)) int32EquivToFin.symm


protected def standardType : StandardType (State) Var Int32 (Finset Int32) where
  dom _ := Finset.univ
  valid := by
    refine .mk ?_ ?_
    · simp
    · intro var val
      simp
      exists { x := val }

instance concreteStandardType : StandardType.Concrete (State) Var Int32 (Finset Int32) where
  standardType := InterleavingOfProgramGraphs.standardType
  decidableEq := inferInstance
  specToFintype _ := inferInstance

open StandardType

protected def singletonOP : AtomicProp.SingletonOP (State) Var Int32 (Finset Int32) where
  op var val _ := ⟨⟨var, {val}⟩, by
    refine .mk ?_
    dsimp [Concrete.standardTypeAt, Concrete.standardType, InterleavingOfProgramGraphs.standardType]
    simp [StandardTypeStruct.isValueSetSafe_def]⟩
  valid := by
    refine .mk ?_ ?_ <;> simp


instance concreteFiniteStandardType : StandardType.ConcreteFinite (State) Var Int32 (Finset Int32) where
  toConcrete := concreteStandardType
  hasSingletonOP := ⟨InterleavingOfProgramGraphs.singletonOP⟩
  decidableEqVar := inferInstance
  fintypeVar := inferInstance
  --fintypeSpec := inferInstance

inductive TauCond where
  | tau
  deriving DecidableEq, Fintype

--def tauCond : Cond (State) Var Int32 (Finset Int32) :=

instance finiteCondLike : FiniteCondLike TauCond (State) Var Int32 (Finset Int32) where
  toCond _ := Cond.nil
  toCond_Injective := by
    intro _ _ _
    rfl
  fintype := inferInstance

inductive Control1 : Loc1 → TauCond → Act1 → Loc1 → Prop where
  | intro : Control1 .pre .tau .act .post

inductive Control2 : Loc2 → TauCond → Act2 → Loc2 → Prop where
  | intro : Control2 .pre .tau .act .post

@[reducible]
def pg1 : ProgramGraph TauCond (State) Var Int32 (Finset Int32) where
  Loc := Loc1
  Act := Act1
  effect _ st := ⟨2 * st.x⟩
  ctr := Control1
  loc0 := Eq .pre
  g0 := .nil

@[reducible]
def pg2 : ProgramGraph TauCond (State) Var Int32 (Finset Int32) where
  Loc := Loc2
  Act := Act2
  effect _ st := ⟨st.x + 1⟩
  ctr := Control2
  loc0 := Eq .pre
  g0 := .nil

open Relations.Heterogeneous

def interleaving : Interleaving.EvalEquiv State Var Int32 State Var Int32 where
  var := BiUniqueIndicator.refl Var
  val := BiUniqueIndicator.refl Int32
  partialCongruenceVar := PartialCongruence.ofBiUniqueIndicatorRefl Var
  partialCongruenceVal := PartialCongruence.ofBiUniqueIndicatorRefl Int32
  updateOpLeft := State.updateOp
  updateOpRight := State.updateOp
  valid := by
    refine .mk ?_ ?_ <;> simp [funHEq_iff, BiUniqueIndicator.refl, BiUniqueIndicator.rel_def]
    · intro st; exists st; simp
    · intro st; exists st; simp

@[reducible]
def pg : ProgramGraph (interleaving.CondUnion TauCond TauCond) (interleaving.EvalInter State State) (SumUnion interleaving.var.Rel) (SumUnion interleaving.val.Rel) (SetLikeUnion interleaving.val.Rel (Finset Int32) (Finset Int32)) :=
  interleaving.toProgramGraph pg1 pg2

abbrev PgS : Type _ := interleaving.EvalInter State State

namespace PgS

protected def mk (st: State) : PgS := Interleaving.EvalInter.mk st st (by
  simp [funHEq_iff, interleaving, BiUniqueIndicator.refl, BiUniqueIndicator.rel_def])

end PgS

@[reducible]
def ts : TransitionSystem := pg.toTransitionSystem

abbrev TrS : Type _ := ts.S

namespace TrS

protected def mk (l1: Loc1) (l2: Loc2) (st: State) : TrS := ⟨⟨l1, l2⟩, PgS.mk st⟩

end TrS

open Interleaving.EvalEquiv

open PropositionalLogics

theorem example1 : (TrS.mk .pre .pre ⟨3⟩) ∈ ts.I := by
  dsimp [TrS.mk]
  refine ⟨?_, ?_⟩
  · simp [Loc0]
  · simp [pl_simp]


theorem example2 : ∃(act: ts.Act), (TrS.mk .pre .pre ⟨3⟩) ─⌞act⌟→{ts} (TrS.mk .post .pre ⟨6⟩) := by
  dsimp
  exists (.inl .act)
  dsimp [TrS.mk, pg]
  refine .intro _ _ ?g _ _ ?_ ?_
  case g => exact (.ofSum (.inl .tau))
  · dsimp
    refine .left _ _ _ ?_
    refine .intro
  · simp [pl_simp, FiniteCondLike.toCond]
    --simp [pl_simp, FiniteCondLike.toCond, formulaOfLeft]





end Examples.InterleavingOfProgramGraphs

end
