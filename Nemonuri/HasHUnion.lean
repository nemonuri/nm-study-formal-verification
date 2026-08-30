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


instance (priority := low) {T1 T2: Type u1} {T3: Type u2} [HasHUnion T1 T2 T3] : HasHUnion T2 T1 T3 where
  fst := HasHUnion.snd T1
  snd := HasHUnion.fst T2

/-
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

abbrev DecidableEmbedRange (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2 T3] : Type u2 := (lb: Label) → (rv: T3) → (Decidable (rv ∈ EmbedRangeAt T1 T2 lb))

namespace DecidableEmbedRange

variable [HasHUnion T1 T2 T3]

def isInEmbedRangeAt [DecidableEmbedRange T1 T2 T3] (rv: T3) (lb: Label) : Bool := decide (rv ∈ EmbedRangeAt T1 T2 lb)

theorem isInEmbedRangeAt_eq_true_iff {T1 T2: Type u1} {T3: Type u2} [HasHUnion T1 T2 T3] [DecidableEmbedRange T1 T2 T3] {rv: T3} {lb: Label}
  : (isInEmbedRangeAt T1 T2 rv lb = .true) ↔ (rv ∈ EmbedRangeAt T1 T2 lb) := by
  dsimp [isInEmbedRangeAt]
  rw [decide_eq_true_iff]

theorem isInEmbedRangeAt_eq_false_iff {T1 T2: Type u1} {T3: Type u2} [HasHUnion T1 T2 T3] [DecidableEmbedRange T1 T2 T3] {rv: T3} {lb: Label}
  : (isInEmbedRangeAt T1 T2 rv lb = .false) ↔ (rv ∉ EmbedRangeAt T1 T2 lb) := by
  refine Decidable.not_iff_not.mp ?_
  simp
  exact isInEmbedRangeAt_eq_true_iff

end DecidableEmbedRange


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

abbrev HUnionElemAt (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2 T3] : Type u2 := Set.Elem (hunionSetUnivAt T1 T2)


def hinterSet (s1: Set T1) (s2: Set T2) : Set T3 := (s1.image (embedAt T1 T2 .fst)) ∩ (s2.image (embedAt T1 T2 .snd))

def hinterSetUnivAt (T1 T2: Type u1) {T3: Type u2} [HasHUnion T1 T2 T3] : Set T3 := hinterSet (Set.univ: Set T1) (Set.univ: Set T2)

open DecidableEmbedRange in
theorem hinterSetUnivAt_mem_iff_isInEmbedRangeAt [DecidableEmbedRange T1 T2 T3] {rv: T3}
  : (rv ∈ hinterSetUnivAt T1 T2) ↔ ((isInEmbedRangeAt T1 T2 rv .fst = .true) ∧ (isInEmbedRangeAt T1 T2 rv .snd = .true)) := by
  simp only [isInEmbedRangeAt_eq_true_iff]
  dsimp [hinterSetUnivAt, hinterSet, EmbedRangeAt]
  simp


abbrev HInterElemAt (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2 T3] : Type u2 := Set.Elem (hinterSetUnivAt T1 T2)




def hdiffSet (s1: Set T1) (s2: Set T2) : Set T3 := (s1.image (embedAt T1 T2 .fst)) \ (s2.image (embedAt T1 T2 .snd))

def hdiffSetUnivAt (T1 T2: Type u1) {T3: Type u2} [HasHUnion T1 T2 T3] : Set T3 := hdiffSet (Set.univ: Set T1) (Set.univ: Set T2)

abbrev HDiffElemAt (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2 T3] : Type u2 := Set.Elem (hdiffSetUnivAt T1 T2)



def hunionFinset [DecidableEq T3] (s1: Finset T1) (s2: Finset T2) : Finset T3 := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))

def hunionFinsetUnivAt (T1 T2: Type u1) {T3: Type u2} [HasHUnion T1 T2 T3] [DecidableEq T3] [Fintype T1] [Fintype T2] : Finset T3 := hunionFinset (Finset.univ: Finset T1) (Finset.univ: Finset T2)

theorem hunionFinsetUnivAt_eq_hunionSetUnivAt [DecidableEq T3] [Fintype T1] [Fintype T2]
  : ((hunionFinsetUnivAt T1 T2): Set T3) = hunionSetUnivAt T1 T2 := by
  dsimp [hunionFinsetUnivAt, hunionSetUnivAt, hunionSet, hunionFinset]
  simp


instance hunionFintypeAt (T1 T2: Type u1) [Fintype T1] [Fintype T2] {T3: Type u2} [HasHUnion T1 T2 T3] [DecidableEq T3] : Fintype (HUnionElemAt T1 T2 T3) :=
  have lm2 := @hunionFinsetUnivAt_eq_hunionSetUnivAt T1 T2 T3 _ _ _ _ |> Set.ext_iff.mp
  let embedding : (hunionFinsetUnivAt T1 T2) ↪ (hunionSetUnivAt T1 T2) :=
    {
      toFun x := Subtype.mk x.val (by
        rcases x with ⟨x, lm1⟩
        simp
        exact (lm2 x).mp lm1)
      inj' := by intro _ _; simp
    }
  let elems : Finset (hunionSetUnivAt T1 T2) := (hunionFinsetUnivAt T1 T2: Finset T3).attach.map embedding
  {
    elems := elems
    complete := by
      rintro ⟨x, lm1⟩
      subst elems
      subst embedding
      simp
      exact (lm2 x).mpr lm1
  }


theorem hunionFinset_dist [DecidableEq T3] {s1: Finset T1} {s2: Finset T2}
  : (hunionFinset s1 s2: Set T3) = (hunionSet (s1: Set T1) (s2: Set T2)) := by
  dsimp [hunionFinset, hunionSet]
  simp

instance (priority := low) [dec: (rv: T3) → Decidable (rv ∈ Set.range (HasHUnion.fst T2: T1 → T3))] rv : Decidable (rv ∈ EmbedRangeAt T1 T2 .fst) := dec rv

instance (priority := low) [dec: (rv: T3) → Decidable (rv ∈ Set.range (HasHUnion.snd T1: T2 → T3))] rv : Decidable (rv ∈ EmbedRangeAt T1 T2 .snd) := dec rv

instance ofFstSnd [decFst: ∀rv, Decidable (rv ∈ EmbedRangeAt T1 T2 .fst)] [decSnd: ∀rv, Decidable (rv ∈ EmbedRangeAt T1 T2 .snd)] lb rv : Decidable (rv ∈ EmbedRangeAt T1 T2 lb) :=
  lb.casesOn (fun rv => decFst rv) (fun rv => decSnd rv) <| rv


open DecidableEmbedRange in
def hunionIndicator [DecidableEmbedRange T1 T2 T3] (s1: T1 → Bool) (s2: T2 → Bool) (rv: T3) : Bool :=
  let loc2 (_: Unit) : Bool :=
    if lm2: isInEmbedRangeAt T1 T2 rv .snd then
      s2 (liftAt T1 T2 rv .snd (isInEmbedRangeAt_eq_true_iff.mp lm2))
    else
      .false
  if lm1: isInEmbedRangeAt T1 T2 rv .fst then
    if s1 (liftAt T1 T2 rv .fst (isInEmbedRangeAt_eq_true_iff.mp lm1)) then
      .true
    else
      loc2 ()
  else
    loc2 ()

open DecidableEmbedRange in
theorem hunionIndicator_eq_true_iff [DecidableEmbedRange T1 T2 T3] {s1: T1 → Bool} {s2: T2 → Bool} {rv: T3}
  : (hunionIndicator s1 s2 rv = .true) ↔ ((∃req1, s1 (liftAt T1 T2 rv .fst req1) = .true) ∨ (∃req2, s2 (liftAt T1 T2 rv .snd req2) = .true)) := by
  cases lm1: isInEmbedRangeAt T1 T2 rv .fst
  <;> cases lm2: isInEmbedRangeAt T1 T2 rv .snd
  <;> simp [lm1, lm2, hunionIndicator]
  <;> (
    revert lm1 lm2
    simp [isInEmbedRangeAt_eq_true_iff, isInEmbedRangeAt_eq_false_iff]
    intro lm1 lm2
    simp [lm1, lm2] )


theorem hunionIndicator_set_eq [DecidableEmbedRange T1 T2 T3] {s1: T1 → Bool} {s2: T2 → Bool}
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


open DecidableEmbedRange in
def hunionMapAt.{u3, u4}
  (DomL1 DomL2: Type u1) (DomR: Type u2) [HasHUnion DomL1 DomL2 DomR] [DecidableEmbedRange DomL1 DomL2 DomR]
  (CodL1 CodL2: Type u3) (CodR: Type u4) [HasHUnion CodL1 CodL2 CodR] [DecidableEmbedRange CodL1 CodL2 CodR]
  (m1: DomL1 → CodL1) (m2: DomL2 → CodL2) (sel: HInterElemAt DomL1 DomL2 DomR → Label)
  (dv: HUnionElemAt DomL1 DomL2 DomR) : CodR :=
  let map1 (req: isInEmbedRangeAt DomL1 DomL2 dv.val .fst = .true) : CodR := m1 (liftAt DomL1 DomL2 dv.val .fst (isInEmbedRangeAt_eq_true_iff.mp req)) |> embedAt CodL1 CodL2 .fst
  let map2 (req: isInEmbedRangeAt DomL1 DomL2 dv.val .snd = .true) : CodR := m2 (liftAt DomL1 DomL2 dv.val .snd (isInEmbedRangeAt_eq_true_iff.mp req)) |> embedAt CodL1 CodL2 .snd
  if lm1: isInEmbedRangeAt DomL1 DomL2 dv.val .fst then
    if lm2: isInEmbedRangeAt DomL1 DomL2 dv.val .snd then
      let lb : Label := sel ⟨dv.val, hinterSetUnivAt_mem_iff_isInEmbedRangeAt.mpr (And.intro lm1 lm2)⟩
      match lb with
      | .fst => map1 lm1
      | .snd => map2 lm2
    else
      map1 lm1
  else if lm2: isInEmbedRangeAt DomL1 DomL2 dv.val .snd then
    map2 lm2
  else
    absurd dv.property (by
      intro lm3
      simp [isInEmbedRangeAt_eq_false_iff, EmbedRangeAt] at lm1 lm2
      rewrite [hunionSetUnivAt_mem_iff] at lm3
      rcases lm3 with lm3 | lm3 <;> (rcases lm3 with ⟨lv, lm3⟩)
      · exact lm1 lv lm3
      · exact lm2 lv lm3)





class Bundle (T1 T2: Type u1) (T3: outParam <| Type u2) where
  hasHUnion: HasHUnion T1 T2 T3
  memDecidable : DecidableEmbedRange T1 T2 T3


--attribute [reducible, instance] Bundle.hasHUnion Bundle.memDecidable


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
