module

public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Embedding.Basic

@[expose] public section

namespace Nemonuri

theorem LiftableEmbedding.apply_mem {T1 T2: Type*} {emb: T1 ↪ T2} {x: T1} : (emb x) ∈ Set.range emb := by simp

open LiftableEmbedding in
structure LiftableEmbedding (T1 T2: Type*) extends toEmbedding: T1 ↪ T2 where
  lift (t2: T2) (req: t2 ∈ Set.range toEmbedding) : T1
  lift_valid (t1: T1) : lift (toEmbedding t1) (apply_mem) = t1

namespace LiftableEmbedding

variable {L R: Type*}

instance toFunlike : FunLike (LiftableEmbedding L R) L R where
  coe x := (x.toEmbedding: L → R)
  coe_injective := by
    rintro ⟨emb, lift1, lm1⟩ ⟨emb2, lift2, lm2⟩
    simp
    intro lm3
    subst lm3
    simp [funext_iff]
    intro t2 t1 lm3
    have lm4 := lm3.symm
    subst lm4
    revert lm3; simp
    specialize lm1 t1
    specialize lm2 t1
    rw [lm1, lm2]

instance : EmbeddingLike (LiftableEmbedding L R) L R where
  injective' x := x.toEmbedding.injective

@[defeq]
theorem coe_eq_toEmbedding_coe {l: LiftableEmbedding L R} : (l: L → R) = (l.toEmbedding: L → R) := rfl


def refl (L: Type*) : LiftableEmbedding L L where
  toEmbedding := Function.Embedding.refl L
  lift rv _ := rv
  lift_valid lv := Function.Embedding.refl_apply _ lv

instance decidableRangeMemOfRefl (L: Type*) (rv: L) : Decidable (rv ∈ Set.range (refl L)) :=
  decidable_of_iff True (by simp; exists rv)


def sumLeft (L1 L2: Type*) : LiftableEmbedding L1 (L1 ⊕ L2) :=
  let embedding : Function.Embedding L1 (L1 ⊕ L2) := ⟨Sum.inl, by intro _ _; simp⟩
  {
    toEmbedding := embedding
    lift rv req :=
      rv.casesOn (motive := fun rv => (rv ∈ Set.range embedding) → L1)
        (fun l1 _ => l1)
        (fun l2 h => absurd h (by simp))
      <| req
    lift_valid := by subst embedding; simp
  }


instance decidableRangeMemOfSumLeft (L1 L2: Type*) rv : Decidable (rv ∈ Set.range (sumLeft L1 L2)) :=
  decidable_of_iff (rv.isLeft = .true) (by
    dsimp [sumLeft, coe_eq_toEmbedding_coe]
    simp only [Set.mem_range, Sum.isLeft_iff]
    conv => lhs; arg 1; ext; rw [Eq.comm] )


def sumRight (L1 L2: Type*) : LiftableEmbedding L2 (L1 ⊕ L2) :=
  let embedding : Function.Embedding L2 (L1 ⊕ L2) := ⟨Sum.inr, by intro _ _; simp⟩
  {
    toEmbedding := embedding
    lift rv req :=
      rv.casesOn (motive := fun rv => (rv ∈ Set.range embedding) → L2)
        (fun l1 h => absurd h (by simp))
        (fun l2 _ => l2)
      <| req
    lift_valid := by subst embedding; simp
  }

instance decidableRangeMemOfSumRight (L1 L2: Type*) rv : Decidable (rv ∈ Set.range (sumRight L1 L2)) :=
  decidable_of_iff (rv.isRight = .true) (by
    dsimp [sumRight, coe_eq_toEmbedding_coe]
    simp only [Set.mem_range, Sum.isRight_iff]
    conv => lhs; arg 1; ext; rw [Eq.comm] )

end LiftableEmbedding


class HasHUnion.{u1, u2} (T1 T2: Type u1) (T3: outParam <| Type u2) where
  fst: LiftableEmbedding.{u1, u2} T1 T3
  snd: LiftableEmbedding.{u1, u2} T2 T3

namespace HasHUnion

inductive Label where
  | fst
  | snd
  deriving DecidableEq

universe u1 u2

/-
class HasPartialLift (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2 T3] where
  fst: LiftableEmbedding.PartialLift (@HasHUnion.fst T1 T2 T3 _)
  snd: LiftableEmbedding.PartialLift (@HasHUnion.snd T1 T2 T3 _)
-/

section TypeAbbrev

variable (T1 T2: Type u1) (T3: Type u2)

abbrev LeftTypeAt [HasHUnion T1 T2 T3] (lb: Label) : Type u1 :=
  Label.casesOn lb T1 T2

abbrev LiftableEmbeddingTypeAt [HasHUnion T1 T2 T3] (lb: Label) : Type (max u1 u2) := LiftableEmbedding.{u1, u2} (LeftTypeAt T1 T2 T3 lb) T3

def toLiftableEmbeddingAt [HasHUnion T1 T2 T3] (lb: Label) : LiftableEmbeddingTypeAt T1 T2 T3 lb :=
  Label.casesOn lb (HasHUnion.fst T2) (HasHUnion.snd T1)

end TypeAbbrev

/-
variable {T1 T2: Type u1} {T3: Type u2}

instance (priority := low) [HasHUnion T1 T2 T3] : HasHUnion T2 T1 T3 where
  fst := HasHUnion.snd T1
  snd := HasHUnion.fst T2

instance (priority := low) [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] : HasPartialLift T2 T1 T3 where
  fst := HasPartialLift.snd
  snd := HasPartialLift.fst
-/

section ExplicitLeftType

variable (T1 T2: Type u1) {T3: Type u2}

def embedAt [HasHUnion T1 T2 T3] (lb: Label) (lv: LeftTypeAt T1 T2 T3 lb) : T3 := (toLiftableEmbeddingAt T1 T2 T3 lb) lv

theorem embedAt_injective [HasHUnion T1 T2 T3] {lb: Label} : Function.Injective (embedAt T1 T2 lb) := by
  intro x1 x2 lm1
  dsimp [LeftTypeAt] at x1 x2
  dsimp [embedAt, toLiftableEmbeddingAt] at lm1
  cases lb <;> (
    dsimp at x1 x2 lm1
    exact (Function.Embedding.injective _).eq_iff.mp lm1 )

def EmbedRangeAt [HasHUnion T1 T2 T3] (lb: Label) : Set T3 := Set.range (embedAt T1 T2 lb)

def liftAt [HasHUnion T1 T2 T3] (rv: T3) (lb: Label) (req: rv ∈ EmbedRangeAt T1 T2 lb) : LeftTypeAt T1 T2 T3 lb :=
  (toLiftableEmbeddingAt T1 T2 T3 lb).lift rv req


theorem embedAt_liftAt_eq [HasHUnion T1 T2 T3] {lb: Label} {lv: LeftTypeAt T1 T2 T3 lb}
  : liftAt T1 T2 (embedAt T1 T2 lb lv) lb (Set.mem_range_self _) = lv :=
  (toLiftableEmbeddingAt T1 T2 T3 lb).lift_valid lv

end ExplicitLeftType


instance ofRefl (T: Type u1) : HasHUnion T T T where
  fst := .refl T
  snd := .refl T

instance ofSum (L1 L2: Type u1) : HasHUnion L1 L2 (L1 ⊕ L2) where
  fst := .sumLeft L1 L2
  snd := .sumRight L1 L2




variable {T1 T2: Type u1} {T3: Type u2} [HasHUnion T1 T2 T3]

def hunionSet (s1: Set T1) (s2: Set T2) : Set T3 := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))

def hunionSetUnivAt (T1 T2: Type u1) {T3: Type u2} [HasHUnion T1 T2 T3] : Set T3 := hunionSet (Set.univ: Set T1) (Set.univ: Set T2)

theorem hunionSetUnivAt_mem_iff {rv: T3} : (rv ∈ hunionSetUnivAt T1 T2) ↔ ((∃lv1, embedAt T1 T2 .fst lv1 = rv) ∨ (∃lv2, embedAt T1 T2 .snd lv2 = rv)) := by
  dsimp [hunionSetUnivAt, hunionSet]
  simp

def hunionFinset [DecidableEq T3] (s1: Finset T1) (s2: Finset T2) : Finset T3 := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))


theorem hunionFinset_dist [DecidableEq T3] {s1: Finset T1} {s2: Finset T2}
  : (hunionFinset s1 s2: Set T3) = (hunionSet (s1: Set T1) (s2: Set T2)) := by
  dsimp [hunionFinset, hunionSet]
  simp

instance (priority := low) [dec: (rv: T3) → Decidable (rv ∈ Set.range (HasHUnion.fst T2: T1 → T3))] rv : Decidable (rv ∈ EmbedRangeAt T1 T2 .fst) := dec rv

instance (priority := low) [dec: (rv: T3) → Decidable (rv ∈ Set.range (HasHUnion.snd T1: T2 → T3))] rv : Decidable (rv ∈ EmbedRangeAt T1 T2 .snd) := dec rv

instance ofFstSnd [decFst: ∀rv, Decidable (rv ∈ EmbedRangeAt T1 T2 .fst)] [decSnd: ∀rv, Decidable (rv ∈ EmbedRangeAt T1 T2 .snd)] lb rv : Decidable (rv ∈ EmbedRangeAt T1 T2 lb) :=
  lb.casesOn (fun rv => decFst rv) (fun rv => decSnd rv) <| rv


def hunionIndicator [∀lb rv, Decidable (rv ∈ EmbedRangeAt T1 T2 lb)] (s1: T1 → Bool) (s2: T2 → Bool) (rv: T3) : Bool :=
  let loc2 (_: Unit) : Bool :=
    if lm2: decide (rv ∈ EmbedRangeAt T1 T2 .snd) then
      s2 (liftAt T1 T2 rv .snd (decide_eq_true_iff.mp lm2))
    else
      .false
  if lm1: decide (rv ∈ EmbedRangeAt T1 T2 .fst) then
    if s1 (liftAt T1 T2 rv .fst (decide_eq_true_iff.mp lm1)) then
      .true
    else
      loc2 ()
  else
    loc2 ()


theorem hunionIndicator_eq_true_iff [∀lb rv, Decidable (rv ∈ EmbedRangeAt T1 T2 lb)] {s1: T1 → Bool} {s2: T2 → Bool} {rv: T3}
  : (hunionIndicator s1 s2 rv = .true) ↔ ((∃req1, s1 (liftAt T1 T2 rv .fst req1) = .true) ∨ (∃req2, s2 (liftAt T1 T2 rv .snd req2) = .true)) := by
  cases lm1: decide (rv ∈ EmbedRangeAt T1 T2 .fst)
  <;> cases lm2: decide (rv ∈ EmbedRangeAt T1 T2 .snd)
  <;> (simp at lm1 lm2; simp [lm1, lm2, hunionIndicator])

theorem hunionIndicator_set_eq [∀lb rv, Decidable (rv ∈ EmbedRangeAt T1 T2 lb)] {s1: T1 → Bool} {s2: T2 → Bool}
  : { t3 | hunionIndicator s1 s2 t3 = .true } = (hunionSet { t1 | s1 t1 = .true } { t2 | s2 t2 = .true }) := by
  simp [hunionSet, Set.ext_iff]
  intro rv
  simp [hunionIndicator_eq_true_iff, EmbedRangeAt, LeftTypeAt]
  constructor
  · intro lm1
    rcases lm1 with lm1 | lm1
    <;> (
      rcases lm1 with ⟨⟨lv, lm1⟩, lm2⟩
      have lm3 := lm1.symm
      subst lm3
      rewrite [embedAt_liftAt_eq] at lm2
      clear lm1 )
    · refine Or.inl ?_
      exists lv
    · refine Or.inr ?_
      exists lv
  · intro lm1
    rcases lm1 with lm1 | lm1
    <;> (
      rcases lm1 with ⟨lv, lm1, lm2⟩
      replace lm2 := lm2.symm
      subst lm2
      simp [embedAt_liftAt_eq, lm1] )


class Bundle (T1 T2: Type u1) (T3: outParam <| Type u2) where
  hasHUnion: HasHUnion T1 T2 T3
  memDecidable (lb: Label) (rv: T3) : Decidable (rv ∈ EmbedRangeAt T1 T2 lb)

attribute [reducible, instance] Bundle.hasHUnion Bundle.memDecidable

namespace Bundle

open LiftableEmbedding

@[reducible]
def ofRefl (T: Type*) : Bundle T T T :=
  let hu := HasHUnion.ofRefl T
  {
    hasHUnion := hu
    memDecidable := @ofFstSnd T T T _ (decidableRangeMemOfRefl T) (decidableRangeMemOfRefl T)
  }

@[reducible]
def ofSum (L1 L2: Type u1) : Bundle L1 L2 (L1 ⊕ L2) :=
  let hu := HasHUnion.ofSum L1 L2
  {
    hasHUnion := hu
    memDecidable := @ofFstSnd L1 L2 _ hu (decidableRangeMemOfSumLeft L1 L2) (decidableRangeMemOfSumRight L1 L2)
  }



end Bundle

end HasHUnion


end Nemonuri

end
