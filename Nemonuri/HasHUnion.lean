module

public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Embedding.Basic

@[expose] public section

set_option autoImplicit false

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

def liftAlt (l: LiftableEmbedding L R) (rv: { rv: R // rv ∈ Set.range l }) : L := l.lift rv.val rv.property

@[defeq]
theorem lift_eq_liftAlt {l: LiftableEmbedding L R} {rv: R} {req: rv ∈ Set.range l}
  : l.lift rv req = l.liftAlt ⟨rv, req⟩ :=
  rfl

theorem liftAlt_Injective {l: LiftableEmbedding L R} : Function.Injective (liftAlt l) := by
  rintro ⟨rv1, lm1⟩ ⟨rv2, lm2⟩ lm3
  revert lm1 lm2
  simp [liftAlt]
  intro lv1 lm1 lv2 lm2 lm3
  have lm1_1 := lm1.symm
  have lm2_1 := lm2.symm
  subst lm1_1 lm2_1
  revert lm1 lm2
  simp
  intro lm3
  simp only [coe_eq_toEmbedding_coe, LiftableEmbedding.lift_valid] at lm3
  exact lm3

theorem liftAlt_dom_congr {l: LiftableEmbedding L R} {rv1 rv2: R} (req1: rv1 = rv2) (req2: rv1 ∈ Set.range l)
  : ((Subtype.mk rv1 req2) = (Subtype.mk rv2 (req1 ▸ req2))) := by
  simpa using req1



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


class HasHUnion.{u1, u2} (L1 L2: Type u1) where
  R: Type u2
  fst: LiftableEmbedding.{u1, u2} L1 R
  snd: LiftableEmbedding.{u1, u2} L2 R

namespace HasHUnion

inductive Label where
  | fst
  | snd
  deriving DecidableEq

namespace Label

instance : Nonempty Label := .intro .fst

abbrev toDual (lb: Label) : Label := lb.casesOn Label.snd Label.fst

theorem ne_iff_eq_toDual {lb1 lb2: Label} : (lb1 ≠ lb2) ↔ (lb1 = lb2.toDual) := by
  dsimp [toDual]
  rcases lb1 <;> rcases lb2 <;> simp
/-
  constructor
  · intro lm1
    dsimp [toDual]
    cases lb1 <;> cases lb2
    · simp at lm1
    · simp
    · simp
    · simp at lm1
  · intro lm1
    dsimp [toDual] at lm1
    cases lb2 <;> (dsimp at lm1; subst lm1; simp)
-/

theorem toDual_toDual_eq_self {lb: Label} : lb.toDual.toDual = lb := by
  rcases lb <;> dsimp [toDual]

theorem eq_toDual_symm {lb1 lb2: Label} (req: lb1 = lb2.toDual) : lb2 = lb1.toDual := by
  replace req := congrArg (Label.toDual) req
  simp [toDual_toDual_eq_self] at req
  exact req.symm

theorem ne_iff_eq_toDual_symm {lb1 lb2: Label} : (lb1 ≠ lb2) ↔ (lb2 = lb1.toDual) := by
  rw [ne_iff_eq_toDual]
  constructor
  · intro lm1
    exact eq_toDual_symm lm1
  · intro lm1
    exact eq_toDual_symm lm1

def projectProd (lb: Label) {α β: Type _} (prod: α × β) : lb.casesOn α β := lb.casesOn prod.fst prod.snd

section ProjectProd

variable {α β: Type _} {prod: α × β}

@[defeq]
theorem projectProd_prod_eq
  : (Label.fst.projectProd prod, Label.snd.projectProd prod) = prod := by
  dsimp [projectProd]

@[defeq]
theorem projectProd_prod_fst_eq
  : Label.fst.projectProd prod = prod.fst := by
  dsimp [projectProd]

@[defeq]
theorem projectProd_prod_snd_eq
  : Label.snd.projectProd prod = prod.snd := by
  dsimp [projectProd]

end ProjectProd

end Label

universe u1 u2

/-
class HasPartialLift (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2] where
  fst: LiftableEmbedding.PartialLift (@HasHUnion.fst T1 T2 T3 _)
  snd: LiftableEmbedding.PartialLift (@HasHUnion.snd T1 T2 T3 _)
-/

section TypeAbbrev

variable (T1 T2: Type u1) --(T3: Type u2)

abbrev LeftTypeAt [HasHUnion T1 T2] (lb: Label) : Type u1 :=
  Label.casesOn lb T1 T2

abbrev LiftableEmbeddingTypeAt [HasHUnion T1 T2] (lb: Label) : Type (max u1 u2) := LiftableEmbedding.{u1, u2} (LeftTypeAt T1 T2 lb) (HasHUnion.R T1 T2)

def toLiftableEmbeddingAt [HasHUnion T1 T2] (lb: Label) : LiftableEmbeddingTypeAt T1 T2 lb :=
  Label.casesOn lb (HasHUnion.fst) (HasHUnion.snd)

end TypeAbbrev


instance (priority := low) {T1 T2: Type u1} [HasHUnion T1 T2] : HasHUnion T2 T1 where
  R := HasHUnion.R T1 T2
  fst := HasHUnion.snd
  snd := HasHUnion.fst

/-
instance (priority := low) [HasHUnion T1 T2] [HasPartialLift T1 T2 T3] : HasPartialLift T2 T1 T3 where
  fst := HasPartialLift.snd
  snd := HasPartialLift.fst
-/

section ExplicitLeftType

variable (T1 T2: Type u1) --{T3: Type u2}

def embedAt [HasHUnion T1 T2] (lb: Label) (lv: LeftTypeAt T1 T2 lb) : R T1 T2 := (toLiftableEmbeddingAt T1 T2 lb) lv

theorem embedAt_injective {T1 T2: Type u1} [HasHUnion T1 T2] {lb: Label} : Function.Injective (embedAt T1 T2 lb) := by
  intro x1 x2 lm1
  dsimp [LeftTypeAt] at x1 x2
  dsimp [embedAt, toLiftableEmbeddingAt] at lm1
  cases lb <;> (
    dsimp at x1 x2 lm1
    exact (Function.Embedding.injective _).eq_iff.mp lm1 )

theorem embedAt_injective_at {T1 T2: Type u1} [HasHUnion T1 T2] (lb: Label) : Function.Injective (embedAt T1 T2 lb) := embedAt_injective

def EmbedRangeAt [HasHUnion T1 T2] (lb: Label) : Set (R T1 T2) := Set.range (embedAt T1 T2 lb)

namespace EmbedRangeAt

variable {T1 T2: Type u1} [HasHUnion T1 T2] {lb: Label}

@[simp]
theorem mem_self {lv: LeftTypeAt T1 T2 lb} : embedAt T1 T2 lb lv ∈ EmbedRangeAt T1 T2 lb := by
  dsimp [EmbedRangeAt]
  exact Set.mem_range_self _

theorem exists_embedAt_iff {rv: R T1 T2}
  : (rv ∈ EmbedRangeAt T1 T2 lb) ↔ (∃(lv: LeftTypeAt T1 T2 lb), embedAt T1 T2 lb lv = rv) := by
  simp [EmbedRangeAt]

end EmbedRangeAt

abbrev DecidableEmbedRange (T1 T2: Type u1) [HasHUnion T1 T2] : Type u2 := (lb: Label) → (rv: R T1 T2) → (Decidable (rv ∈ EmbedRangeAt T1 T2 lb))

namespace DecidableEmbedRange

variable [HasHUnion T1 T2]

def isInEmbedRangeAt [DecidableEmbedRange T1 T2] (rv: R T1 T2) (lb: Label) : Bool := decide (rv ∈ EmbedRangeAt T1 T2 lb)

theorem isInEmbedRangeAt_eq_true_iff {T1 T2: Type u1} [HasHUnion T1 T2] [DecidableEmbedRange T1 T2] {rv: R T1 T2} {lb: Label}
  : (isInEmbedRangeAt T1 T2 rv lb = .true) ↔ (rv ∈ EmbedRangeAt T1 T2 lb) := by
  dsimp [isInEmbedRangeAt]
  rw [decide_eq_true_iff]

theorem isInEmbedRangeAt_eq_false_iff {T1 T2: Type u1} [HasHUnion T1 T2] [DecidableEmbedRange T1 T2] {rv: R T1 T2} {lb: Label}
  : (isInEmbedRangeAt T1 T2 rv lb = .false) ↔ (rv ∉ EmbedRangeAt T1 T2 lb) := by
  refine Decidable.not_iff_not.mp ?_
  simp
  exact isInEmbedRangeAt_eq_true_iff

noncomputable instance ofClassicalAt : DecidableEmbedRange T1 T2 := fun _ _ => Classical.propDecidable _


end DecidableEmbedRange


def liftAt [HasHUnion T1 T2] (rv: R T1 T2) (lb: Label) (req: rv ∈ EmbedRangeAt T1 T2 lb) : LeftTypeAt T1 T2 lb :=
  (toLiftableEmbeddingAt T1 T2 lb).lift rv req

def liftAtAlt [HasHUnion T1 T2] (lb: Label) (rv: { rv: R T1 T2 // rv ∈ EmbedRangeAt T1 T2 lb }) : LeftTypeAt T1 T2 lb :=
  liftAt T1 T2 rv.val lb rv.property


theorem liftAtAlt_injective {T1 T2: Type u1} [HasHUnion T1 T2] {lb: Label} : Function.Injective (liftAtAlt T1 T2 lb) := by
  rintro ⟨rv1, lm1⟩ ⟨rv2, lm2⟩ lm3
  dsimp [liftAtAlt, liftAt, LiftableEmbedding.lift_eq_liftAlt] at lm3
  rewrite [LiftableEmbedding.liftAlt_Injective.eq_iff] at lm3
  exact lm3

theorem liftAlt_dom_congr {T1 T2: Type u1} [HasHUnion T1 T2] {rv1 rv2: R T1 T2} (req1: rv1 = rv2) {lb: Label} (req2: rv1 ∈ EmbedRangeAt T1 T2 lb)
  : (Subtype.mk rv1 req2) = (Subtype.mk rv2 (req1 ▸ req2)) :=
  LiftableEmbedding.liftAlt_dom_congr req1 req2


theorem embedAt_liftAt_eq [HasHUnion T1 T2] {lb: Label} {lv: LeftTypeAt T1 T2 lb}
  : liftAt T1 T2 (embedAt T1 T2 lb lv) lb (Set.mem_range_self _) = lv :=
  (toLiftableEmbeddingAt T1 T2 lb).lift_valid lv

@[defeq]
theorem liftAt_eq_liftAtAlt [HasHUnion T1 T2] {rv: R T1 T2} {lb: Label} {req: rv ∈ EmbedRangeAt T1 T2 lb}
  : liftAt T1 T2 rv lb req = liftAtAlt T1 T2 lb ⟨rv, req⟩ :=
  rfl


theorem liftAt_embedAt_eq [HasHUnion T1 T2] {rv: R T1 T2} {lb: Label} (req: rv ∈ EmbedRangeAt T1 T2 lb)
  : embedAt T1 T2 lb (liftAt T1 T2 rv lb req) = rv := by
  refine @Subtype.mk.inj _ _ _ ?_ rv req ?_
  · exact EmbedRangeAt.mem_self
  · rw [← liftAtAlt_injective.eq_iff, ← liftAt_eq_liftAtAlt, embedAt_liftAt_eq]
    rw [liftAt_eq_liftAtAlt]


theorem eq_toDual_liftAt_embedAt_of_eq
  {T1 T2: Type u1} [HasHUnion T1 T2] {rv1 rv2: R T1 T2} (req1: rv1 = rv2)
  {lb: Label} (req2: rv1 ∈ EmbedRangeAt T1 T2 lb) (req3: rv2 ∈ EmbedRangeAt T1 T2 lb.toDual)
  : embedAt T1 T2 lb (liftAt T1 T2 rv1 lb req2) = embedAt T1 T2 lb.toDual (liftAt T1 T2 rv2 lb.toDual req3) := by
  simp only [liftAt_embedAt_eq]
  exact req1

theorem liftAt_eq_of_embedAt_eq
  {T1 T2: Type u1} [HasHUnion T1 T2] {rv: R T1 T2} {lb: Label} {lv: LeftTypeAt T1 T2 lb} (req: embedAt T1 T2 lb lv = rv)
  : liftAt T1 T2 rv lb (req.subst EmbedRangeAt.mem_self) = lv := by
  have lm1 := req.symm
  subst lm1
  rw [embedAt_liftAt_eq]


theorem embedAt_eq_iff_liftAt_eq
  {T1 T2: Type u1} [HasHUnion T1 T2] {rv: R T1 T2} {lb: Label} {lv: LeftTypeAt T1 T2 lb} (req: rv ∈ EmbedRangeAt T1 T2 lb)
  : (embedAt T1 T2 lb lv = rv) ↔ (liftAt T1 T2 rv lb req = lv) := by
  constructor
  · intro lm1
    exact liftAt_eq_of_embedAt_eq lm1
  · intro lm1
    have lm2 := lm1.symm
    subst lm2
    rw [liftAt_embedAt_eq]

theorem embedAt_eq_iff_exists_liftAt_eq
  {T1 T2: Type u1} [HasHUnion T1 T2] {rv: R T1 T2} {lb: Label} {lv: LeftTypeAt T1 T2 lb}
  : (embedAt T1 T2 lb lv = rv) ↔ (∃req, liftAt T1 T2 rv lb req = lv) := by
  constructor
  · intro lm1
    refine ⟨?_, ?_⟩
    · simp [← lm1]
    · exact liftAt_eq_of_embedAt_eq lm1
  · rintro ⟨lm1, lm2⟩
    exact (embedAt_eq_iff_liftAt_eq lm1).mpr lm2

/-
structure AreEquiv {T1 T2: Type u1} [HasHUnion T1 T2] (lv1: T1) (lv2: T2) (rv: HasHUnion.R T1 T2) : Prop where
  inter (lb: Label) : rv ∈ EmbedRangeAt T1 T2 lb
  liftAt_eq_fst: liftAt T1 T2 rv .fst (inter .fst) = lv1
  liftAt_eq_snd: liftAt T1 T2 rv .snd (inter .snd) = lv2
-/

inductive AreEquivAt {T1 T2: Type u1} [HasHUnion T1 T2] (lv1: T1) (lv2: T2) : Label → Prop where
  | fst (req1: embedAt T1 T2 .fst lv1 ∈ EmbedRangeAt T1 T2 .snd) (req2: liftAt T1 T2 (embedAt T1 T2 .fst lv1) .snd req1 = lv2)
        : AreEquivAt lv1 lv2 .fst
  | snd (req1: embedAt T1 T2 .snd lv2 ∈ EmbedRangeAt T1 T2 .fst) (req2: liftAt T1 T2 (embedAt T1 T2 .snd lv2) .fst req1 = lv1)
        : AreEquivAt lv1 lv2 .snd--(embedAt T1 T2 .snd lv2)

def AreEquiv {T1 T2: Type u1} [HasHUnion T1 T2] (lv1: T1) (lv2: T2) : Prop := ∀⦃lb: Label⦄, AreEquivAt lv1 lv2 lb

@[defeq]
theorem areEquiv_eq_areEquivAt {T1 T2: Type u1} [HasHUnion T1 T2] {lv1: T1} {lv2: T2}
  : AreEquiv lv1 lv2 = ((lb: Label) → AreEquivAt lv1 lv2 lb) :=
  rfl

namespace AreEquivAt

variable {T1 T2: Type u1} [HasHUnion T1 T2] {lv1: T1} {lv2: T2}

theorem fst_iff
  : (AreEquivAt lv1 lv2 .fst) ↔ (∃(req: embedAt T1 T2 .fst lv1 ∈ EmbedRangeAt T1 T2 .snd), liftAt T1 T2 (embedAt T1 T2 .fst lv1) .snd req = lv2) := by
  constructor
  · intro lm1
    rcases lm1 with ⟨lm1, lm2⟩ | _
    · exact ⟨lm1, lm2⟩
  · rintro ⟨lm1, lm2⟩
    exact .fst lm1 lm2

theorem snd_iff
  : (AreEquivAt lv1 lv2 .snd) ↔ (∃(req: embedAt T1 T2 .snd lv2 ∈ EmbedRangeAt T1 T2 .fst), liftAt T1 T2 (embedAt T1 T2 .snd lv2) .fst req = lv1) := by
  constructor
  · intro lm1
    rcases lm1 with _ | ⟨lm1, lm2⟩
    · exact ⟨lm1, lm2⟩
  · rintro ⟨lm1, lm2⟩
    exact .snd lm1 lm2

variable {lb: Label}

theorem toDual_iff
  : (AreEquivAt lv1 lv2 lb) ↔ ∃(req: embedAt T1 T2 lb (lb.casesOn lv1 lv2) ∈ EmbedRangeAt T1 T2 lb.toDual), liftAt T1 T2 (embedAt T1 T2 lb (lb.casesOn lv1 lv2)) lb.toDual req = lb.toDual.casesOn lv1 lv2 := by
  rcases lb <;> dsimp [Label.toDual]
  · exact fst_iff
  · exact snd_iff

def rightValue (_: AreEquivAt lv1 lv2 lb) : HasHUnion.R T1 T2 := embedAt T1 T2 lb (lb.casesOn lv1 lv2)

theorem rightValue_embedRangeAt_mem (h: AreEquivAt lv1 lv2 lb) : h.rightValue ∈ EmbedRangeAt T1 T2 lb := by
  simp only [rightValue, EmbedRangeAt.mem_self]

theorem rightValue_toDual_embedRangeAt_mem (h: AreEquivAt lv1 lv2 lb) : h.rightValue ∈ EmbedRangeAt T1 T2 lb.toDual := by
  dsimp [rightValue]
  obtain ⟨lm1, lm2⟩ := toDual_iff.mp h
  exact lm1

theorem rightValue_forall_label_embedRangeAt_mem (h: AreEquivAt lv1 lv2 lb) : ∀(lb2: Label), h.rightValue ∈ EmbedRangeAt T1 T2 lb2 := by
  intro lb2
  by_cases lm1: lb = lb2
  · subst lm1
    exact h.rightValue_embedRangeAt_mem
  · simp [Label.ne_iff_eq_toDual_symm] at lm1
    subst lm1
    exact h.rightValue_toDual_embedRangeAt_mem

theorem toDual_of_fst_eq_snd (h: AreEquivAt lv1 lv2 lb) (req: embedAt T1 T2 .fst lv1 = embedAt T1 T2 .snd lv2)
  : AreEquivAt lv1 lv2 lb.toDual := by
  have lm1 := h.rightValue_forall_label_embedRangeAt_mem
  dsimp [rightValue] at lm1
  rcases lb <;> dsimp [Label.toDual] at lm1 ⊢
  · refine .snd ?_ ?_
    · simp [← req]
    · simp [← req, embedAt_liftAt_eq]
  · refine .fst ?_ ?_
    · simp [req]
    · simp [req, embedAt_liftAt_eq]

theorem toDual_iff_fst_eq_snd (h: AreEquivAt lv1 lv2 lb)
  : (AreEquivAt lv1 lv2 lb.toDual) ↔ (embedAt T1 T2 .fst lv1 = embedAt T1 T2 .snd lv2) := by
  constructor
  · intro lm1
    rcases lb <;> dsimp [Label.toDual] at lm1
    · simp [snd_iff, EmbedRangeAt] at lm1
      obtain ⟨⟨lv1_1, lm1⟩, lm2⟩ := lm1
      rewrite [Eq.comm] at lm2 --lm4
      subst lm2
      simp [liftAt_embedAt_eq]
    · simp [snd_iff, EmbedRangeAt] at h
      obtain ⟨⟨lv1_1, lm1⟩, lm2⟩ := h
      rewrite [Eq.comm] at lm2
      subst lm2
      simp [liftAt_embedAt_eq]
  · exact h.toDual_of_fst_eq_snd

end AreEquivAt

namespace AreEquiv

variable {T1 T2: Type u1} [HasHUnion T1 T2] {lv1: T1} {lv2: T2}

theorem mk (req: ∀(lb: Label), AreEquivAt lv1 lv2 lb) : AreEquiv lv1 lv2 := req

theorem apply (h: AreEquiv lv1 lv2) (lb: Label) : AreEquivAt lv1 lv2 lb := @h lb

theorem embedAt_fst_eq_snd (h: AreEquiv lv1 lv2) : embedAt T1 T2 .fst lv1 = embedAt T1 T2 .snd lv2 := by
  have lm1 := h.apply .fst
  refine lm1.toDual_iff_fst_eq_snd.mp ?_
  dsimp [Label.toDual]
  exact h.apply .snd

theorem embedAt_eq_toDual {f: (lb: Label) → LeftTypeAt T1 T2 lb} {lb: Label} (h: AreEquiv (f .fst) (f .snd))
  : embedAt T1 T2 lb (f lb) = embedAt T1 T2 lb.toDual (f lb.toDual) := by
  rcases lb <;> dsimp [Label.toDual]
  · exact h.embedAt_fst_eq_snd
  · exact h.embedAt_fst_eq_snd.symm

end AreEquiv



/-
theorem embedAt_fst_eq_snd_iff_areEquiv_exists
  {T1 T2: Type u1} [HasHUnion T1 T2] {lv1: T1} {lv2: T2}
  : (embedAt T1 T2 .fst lv1 = embedAt T1 T2 .snd lv2) ↔ (∃(rv: R T1 T2), AreEquiv lv1 lv2 rv) := by
  constructor
  · intro lm1
    exists embedAt T1 T2 Label.fst lv1
    refine .mk ?_ ?_ ?_
    · intro lb
      cases lb
      · exact EmbedRangeAt.mem_self
      · rw [lm1]
        exact EmbedRangeAt.mem_self
    · rw [embedAt_liftAt_eq]
    · simp only [lm1]
      rw [embedAt_liftAt_eq]
  · rintro ⟨rv, lm1, lm2, lm3⟩
    rewrite [Eq.comm] at lm2 lm3
    subst lm2
    subst lm3
    refine eq_toDual_liftAt_embedAt_of_eq rfl ?_ ?_
-/


def EmbedElemAt [HasHUnion T1 T2] (lb: Label) : Type u2 := Set.Elem (EmbedRangeAt T1 T2 lb: Set (R T1 T2))

namespace EmbedElemAt

def pureAt [HasHUnion T1 T2] (lb: Label) (lv: LeftTypeAt T1 T2 lb) : EmbedElemAt T1 T2 lb := ⟨embedAt T1 T2 lb lv, by simp only [EmbedRangeAt.mem_self]⟩

def liftAt [HasHUnion T1 T2] (lb: Label) (e: EmbedElemAt T1 T2 lb) : LeftTypeAt T1 T2 lb := HasHUnion.liftAt T1 T2 e.val lb e.property

def bindAt.{u3, u4}
  [HasHUnion T1 T2] (Cod1 Cod2: Type u3) [HasHUnion.{u3, u4} Cod1 Cod2] (lb: Label)
  (rv: EmbedElemAt T1 T2 lb) (f: LeftTypeAt T1 T2 lb → EmbedElemAt Cod1 Cod2 lb) : EmbedElemAt Cod1 Cod2 lb :=
  f (rv.liftAt)

def mapAt.{u3, u4}
  [HasHUnion T1 T2] (Cod1 Cod2: Type u3) [HasHUnion.{u3, u4} Cod1 Cod2] (lb: Label)
  (f: LeftTypeAt T1 T2 lb → LeftTypeAt Cod1 Cod2 lb) (rv: EmbedElemAt T1 T2 lb) : EmbedElemAt Cod1 Cod2 lb :=
  bindAt T1 T2 Cod1 Cod2 lb rv ((pureAt Cod1 Cod2 lb) ∘ f)

end EmbedElemAt


end ExplicitLeftType


instance (priority := low) ofRefl (T: Type u1) : HasHUnion T T where
  R := T
  fst := .refl T
  snd := .refl T

@[reducible]
def ofSum (L1 L2: Type u1) : HasHUnion L1 L2 where
  R := (L1 ⊕ L2)
  fst := .sumLeft L1 L2
  snd := .sumRight L1 L2



variable {T1 T2: Type u1} [HasHUnion T1 T2]


def hunionSet (s1: Set T1) (s2: Set T2) : Set (R T1 T2) := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))

def hunionSetUnivAt (T1 T2: Type u1) [HasHUnion T1 T2] : Set (R T1 T2) := hunionSet (Set.univ: Set T1) (Set.univ: Set T2)

theorem hunionSetUnivAt_mem_iff {rv: R T1 T2} : (rv ∈ hunionSetUnivAt T1 T2) ↔ ((∃lv1, embedAt T1 T2 .fst lv1 = rv) ∨ (∃lv2, embedAt T1 T2 .snd lv2 = rv)) := by
  dsimp [hunionSetUnivAt, hunionSet]
  simp

theorem hunionSetUnivAt_mem_iff_embedRangeAt_mem {rv: R T1 T2} : (rv ∈ hunionSetUnivAt T1 T2) ↔ (∃(lb: Label), rv ∈ EmbedRangeAt T1 T2 lb) := by
  simp [EmbedRangeAt, hunionSetUnivAt_mem_iff]
  constructor
  · intro lm1
    rcases lm1 with lm1 | lm1
    · exists .fst
    · exists .snd
  · rintro ⟨lb, lv, lm1⟩
    cases lb
    · refine Or.inl ?_
      exists lv
    · refine Or.inr ?_
      exists lv

theorem hunionSetUnivAt_mem_of_embedRangeAt_mem {rv: R T1 T2} {lb: Label} (req: rv ∈ EmbedRangeAt T1 T2 lb) : rv ∈ hunionSetUnivAt T1 T2 :=
  hunionSetUnivAt_mem_iff_embedRangeAt_mem.mpr (Exists.intro lb req)


theorem embedAt_hunionSetUnivAt_mem {lb: Label} {lv: LeftTypeAt T1 T2 lb} : embedAt T1 T2 lb lv ∈ hunionSetUnivAt T1 T2 := by
  rw [hunionSetUnivAt_mem_iff_embedRangeAt_mem]
  exists lb
  exact EmbedRangeAt.mem_self


abbrev HUnionElemAt (T1 T2: Type u1) [HasHUnion T1 T2] : Type u2 := Set.Elem (hunionSetUnivAt T1 T2)

namespace HUnionElemAt

def ofEmbedElem {lb: Label} (x: EmbedElemAt T1 T2 lb) : HUnionElemAt T1 T2 := Subtype.mk x.val (by
    have lm1 := x.property
    simp [EmbedRangeAt, - Subtype.coe_prop] at lm1
    rewrite [hunionSetUnivAt_mem_iff]
    cases lb
    · exact Or.inl lm1
    · exact Or.inr lm1 )

def pureAt (T1 T2: Type u1) [HasHUnion T1 T2] (lb: Label) (lv: LeftTypeAt T1 T2 lb) : HUnionElemAt T1 T2 := (ofEmbedElem ∘ EmbedElemAt.pureAt T1 T2 lb) lv

@[defeq]
theorem pureAt_val_eq_embedAt {lb: Label} {lv: LeftTypeAt T1 T2 lb}
  : (pureAt T1 T2 lb lv).val = embedAt T1 T2 lb lv := by
  dsimp [pureAt, EmbedElemAt.pureAt, ofEmbedElem]

@[defeq]
theorem pureAt_eq_embedAt_mk {lb: Label} {lv: LeftTypeAt T1 T2 lb}
  : pureAt T1 T2 lb lv = (Subtype.mk (embedAt T1 T2 lb lv) (embedAt_hunionSetUnivAt_mem)) :=
  Subtype.ext pureAt_val_eq_embedAt

def setOfHUnion (s1: Set T1) (s2: Set T2) : Set (HUnionElemAt T1 T2) :=
  (s1.image (pureAt T1 T2 .fst)) ∪ (s2.image (pureAt T1 T2 .snd))

def liftAt (x: HUnionElemAt T1 T2) (lb: Label) (req: x.val ∈ EmbedRangeAt T1 T2 lb) : LeftTypeAt T1 T2 lb :=
  HasHUnion.liftAt T1 T2 x.val lb req

def liftSetAt (x: Set (HUnionElemAt T1 T2)) (lb: Label) : Set (LeftTypeAt T1 T2 lb) := { lv | pureAt T1 T2 lb lv ∈ x }

def ofRightType (x: R T1 T2) (req: x ∈ hunionSetUnivAt T1 T2) : HUnionElemAt T1 T2 := Subtype.mk x req

/-
def bindAt.{u3, u4}
  [HasHUnion T1 T2] (Cod1 Cod2: Type u3) [HasHUnion.{u3, u4} Cod1 Cod2] (lb: Label)
  (rv: EmbedElemAt T1 T2 lb) (f: LeftTypeAt T1 T2 lb → EmbedElemAt Cod1 Cod2 lb) : EmbedElemAt Cod1 Cod2 lb :=
  f (rv.liftAt)

def mapAt.{u3, u4}
  [HasHUnion T1 T2] (Cod1 Cod2: Type u3) [HasHUnion.{u3, u4} Cod1 Cod2] (lb: Label)
  (f: LeftTypeAt T1 T2 lb → LeftTypeAt Cod1 Cod2 lb) (rv: EmbedElemAt T1 T2 lb) : EmbedElemAt Cod1 Cod2 lb :=
  bindAt T1 T2 Cod1 Cod2 lb rv ((pureAt Cod1 Cod2 lb) ∘ f)
-/

/-
def bindAt.{u3, u4} (Dom1 Dom2: Type u1) [HasHUnion.{u1, u2} Dom1 Dom2] (Cod1 Cod2: Type u3) [HasHUnion.{u3, u4} Cod1 Cod2] (lb: Label)
  (rv: HUnionElemAt Dom1 Dom2) (f: LeftTypeAt Dom1 Dom2 lb → HUnionElemAt Cod1 Cod2) : HUnionElemAt Cod1 Cod2 :=
  f (rv.lif)
-/

end HUnionElemAt


def hinterSet (s1: Set T1) (s2: Set T2) : Set (R T1 T2) := (s1.image (embedAt T1 T2 .fst)) ∩ (s2.image (embedAt T1 T2 .snd))

def hinterSetUnivAt (T1 T2: Type u1) [HasHUnion T1 T2] : Set (R T1 T2) := hinterSet (Set.univ: Set T1) (Set.univ: Set T2)

theorem hinterSetUnivAt_mem_iff {rv: R T1 T2} : (rv ∈ hinterSetUnivAt T1 T2) ↔ ((∃lv1, embedAt T1 T2 .fst lv1 = rv) ∧ (∃lv2, embedAt T1 T2 .snd lv2 = rv)) := by
  dsimp [hinterSetUnivAt, hinterSet]
  simp

theorem hinterSetUnivAt_mem_iff_embedRangeAt_mem {rv: R T1 T2} : (rv ∈ hinterSetUnivAt T1 T2) ↔ (∀lb, rv ∈ EmbedRangeAt T1 T2 lb) := by
  simp [hinterSetUnivAt_mem_iff, EmbedRangeAt]
  constructor
  · rintro ⟨lm1, lm2⟩ lb
    cases lb
    · exact lm1
    · exact lm2
  · intro lm1
    have lm1_1 := lm1 .fst
    have lm1_2 := lm1 .snd
    exact And.intro lm1_1 lm1_2

theorem hinterSetUnivAt_mem_iff_toDual_embedRangeAt_mem {rv: R T1 T2} : (rv ∈ hinterSetUnivAt T1 T2) ↔ (∀(lb: Label), rv ∈ EmbedRangeAt T1 T2 lb.toDual) := by
  rewrite [hinterSetUnivAt_mem_iff_embedRangeAt_mem]
  constructor
  · intro lm1 lb
    exact lm1 lb.toDual
  · intro lm1 lb
    specialize lm1 lb.toDual
    simpa [Label.toDual_toDual_eq_self] using lm1


open DecidableEmbedRange in
theorem hinterSetUnivAt_mem_iff_isInEmbedRangeAt [DecidableEmbedRange T1 T2] {rv: R T1 T2}
  : (rv ∈ hinterSetUnivAt T1 T2) ↔ ((isInEmbedRangeAt T1 T2 rv .fst = .true) ∧ (isInEmbedRangeAt T1 T2 rv .snd = .true)) := by
  simp [isInEmbedRangeAt_eq_true_iff, EmbedRangeAt, hinterSetUnivAt_mem_iff]

theorem embedRangeAt_mem_of_hinterSetUnivAt_mem_at {rv: R T1 T2} (req: rv ∈ hinterSetUnivAt T1 T2) (lb: Label) : rv ∈ EmbedRangeAt T1 T2 lb := by
  simp only [hinterSetUnivAt_mem_iff] at req
  simp [EmbedRangeAt]
  cases lb
  · exact req.left
  · exact req.right

theorem hunionSetUnivAt_mem_of_hinterSetUnivAt_mem {rv: R T1 T2} (req: rv ∈ hinterSetUnivAt T1 T2) : rv ∈ hunionSetUnivAt T1 T2 :=
  embedRangeAt_mem_of_hinterSetUnivAt_mem_at req .fst |> hunionSetUnivAt_mem_of_embedRangeAt_mem

namespace AreEquivAt

theorem fst_of_hinterSetUnivAt_mem {rv: R T1 T2} (req: rv ∈ hinterSetUnivAt T1 T2)
  : letI aux := embedRangeAt_mem_of_hinterSetUnivAt_mem_at req
    AreEquivAt (liftAt T1 T2 rv .fst (aux .fst)) (liftAt T1 T2 rv .snd (aux .snd)) .fst := by
  have lm1 := embedRangeAt_mem_of_hinterSetUnivAt_mem_at req
  refine .fst ?_ ?_
  · dsimp [LeftTypeAt]
    rw [liftAt_embedAt_eq]
    exact lm1 .snd
  · dsimp [LeftTypeAt]
    simp [liftAt_embedAt_eq]

theorem snd_of_hinterSetUnivAt_mem {rv: R T1 T2} (req: rv ∈ hinterSetUnivAt T1 T2)
  : letI aux := embedRangeAt_mem_of_hinterSetUnivAt_mem_at req
    AreEquivAt (liftAt T1 T2 rv .fst (aux .fst)) (liftAt T1 T2 rv .snd (aux .snd)) .snd := by
  have lm1 := embedRangeAt_mem_of_hinterSetUnivAt_mem_at req
  refine .snd ?_ ?_
  · dsimp [LeftTypeAt]
    rw [liftAt_embedAt_eq]
    exact lm1 .fst
  · dsimp [LeftTypeAt]
    simp [liftAt_embedAt_eq]

theorem hinterSetUnivAt_mem_forall_exists {rv: R T1 T2}
  : (rv ∈ hinterSetUnivAt T1 T2) ↔ (∀(lb: Label), ∃req1, ∃req2, AreEquivAt (liftAt T1 T2 rv .fst req1) (liftAt T1 T2 rv .snd req2) lb) := by
  constructor
  · intro lm1 lb
    have lm2 := embedRangeAt_mem_of_hinterSetUnivAt_mem_at lm1
    exists lm2 .fst
    exists lm2 .snd
    rcases lb
    · exact fst_of_hinterSetUnivAt_mem lm1
    · exact snd_of_hinterSetUnivAt_mem lm1
  · intro lm1
    rw [hinterSetUnivAt_mem_iff_toDual_embedRangeAt_mem]
    intro lb
    specialize lm1 lb
    rcases lm1 with ⟨lm1, lm2, lm3⟩
    rcases lb <;> dsimp [Label.toDual]
    · exact lm2
    · exact lm1

end AreEquivAt

namespace AreEquiv

theorem of_hinterSetUnivAt_mem {rv: R T1 T2} (req: rv ∈ hinterSetUnivAt T1 T2)
  : letI aux := embedRangeAt_mem_of_hinterSetUnivAt_mem_at req
    AreEquiv (liftAt T1 T2 rv .fst (aux .fst)) (liftAt T1 T2 rv .snd (aux .snd)) := by
  refine .mk ?_
  intro lb
  rcases lb
  · exact AreEquivAt.fst_of_hinterSetUnivAt_mem req
  · exact AreEquivAt.snd_of_hinterSetUnivAt_mem req

theorem hinterSetUnivAt_mem_iff_exists {rv: R T1 T2}
  : (rv ∈ hinterSetUnivAt T1 T2) ↔ (∃req1, ∃req2, AreEquiv (liftAt T1 T2 rv .fst req1) (liftAt T1 T2 rv .snd req2)) := by
  constructor
  · intro lm1
    have lm2 := embedRangeAt_mem_of_hinterSetUnivAt_mem_at lm1
    exists lm2 .fst
    exists lm2 .snd
    exact of_hinterSetUnivAt_mem lm1
  · rintro ⟨lm1, lm2, lm3⟩
    rw [hinterSetUnivAt_mem_iff_toDual_embedRangeAt_mem]
    intro lb
    rcases lb <;> dsimp [Label.toDual]
    · exact lm2
    · exact lm1

end AreEquiv

abbrev HInterElemAt (T1 T2: Type u1) [HasHUnion T1 T2] : Type u2 := Set.Elem (hinterSetUnivAt T1 T2)

namespace HInterElemAt

def liftAt (x: HInterElemAt T1 T2) (lb: Label) : LeftTypeAt T1 T2 lb :=
  HasHUnion.liftAt T1 T2 x.val lb (embedRangeAt_mem_of_hinterSetUnivAt_mem_at x.property lb)

def toUnion (x: HInterElemAt T1 T2) : HUnionElemAt T1 T2 := Subtype.mk x.val (by
    obtain ⟨x, lm1⟩ := x
    simp [hinterSetUnivAt_mem_iff] at lm1
    simp [hunionSetUnivAt_mem_iff]
    exact Or.inl lm1.left )

def toEmbedElemAt (x: HInterElemAt T1 T2) (lb: Label) : EmbedElemAt T1 T2 lb := EmbedElemAt.pureAt T1 T2 lb (x.liftAt lb)

end HInterElemAt


def hdiffSet (s1: Set T1) (s2: Set T2) (lb: Label) : Set (R T1 T2) :=
  let toSet (lb: Label) : Set (LeftTypeAt T1 T2 lb) := lb.casesOn s1 s2
  ((toSet lb).image (embedAt T1 T2 lb)) \ ((toSet lb.toDual).image (embedAt T1 T2 lb.toDual))


def hdiffSetUnivAt (T1 T2: Type u1) [HasHUnion T1 T2] (lb: Label) : Set (R T1 T2) := hdiffSet (Set.univ: Set T1) (Set.univ: Set T2) lb

theorem hdiffSetUnivAt_mem_iff_embedRangAt_mem {rv: R T1 T2} {lb: Label}
  : (rv ∈ hdiffSetUnivAt T1 T2 lb) ↔ ((rv ∈ EmbedRangeAt T1 T2 lb) ∧ (rv ∉ EmbedRangeAt T1 T2 lb.toDual)) := by
  cases lb <;> ( simp [hdiffSetUnivAt, hdiffSet, Label.toDual, EmbedRangeAt] )


theorem embedRangeAt_mem_of_hdiffSetUnivAt_mem {rv: R T1 T2} {lb: Label} (req: rv ∈ hdiffSetUnivAt T1 T2 lb) : rv ∈ EmbedRangeAt T1 T2 lb :=
  hdiffSetUnivAt_mem_iff_embedRangAt_mem.mp req |>.left

theorem hunionSetUnivAt_mem_of_hdiffSetUnivAt_mem {rv: R T1 T2} {lb: Label} : (rv ∈ hdiffSetUnivAt T1 T2 lb) → (rv ∈ hunionSetUnivAt T1 T2) :=
 hunionSetUnivAt_mem_of_embedRangeAt_mem ∘ embedRangeAt_mem_of_hdiffSetUnivAt_mem


abbrev HDiffElemAt (T1 T2: Type u1) [HasHUnion T1 T2] (lb: Label) : Type u2 := Set.Elem (hdiffSetUnivAt T1 T2 lb)

namespace HDiffElemAt

def toEmbedElem {lb: Label} (x: HDiffElemAt T1 T2 lb) : EmbedElemAt T1 T2 lb := Subtype.mk x.val (embedRangeAt_mem_of_hdiffSetUnivAt_mem x.property)

def toUnion {lb: Label} (x: HDiffElemAt T1 T2 lb) : HUnionElemAt T1 T2 := Subtype.mk x.val (embedRangeAt_mem_of_hdiffSetUnivAt_mem x.property |> hunionSetUnivAt_mem_of_embedRangeAt_mem)

def lift {lb: Label} (x: HDiffElemAt T1 T2 lb) : LeftTypeAt T1 T2 lb := liftAt T1 T2 x.val lb (hdiffSetUnivAt_mem_iff_embedRangAt_mem.mp x.property |>.left)

end HDiffElemAt


namespace HUnionElemAt

open DecidableEmbedRange

@[elab_as_elim]
def recDiffInter [DecidableEmbedRange T1 T2]
  {motive: HUnionElemAt T1 T2 → Sort _}
  (diffFst: (x: HDiffElemAt T1 T2 .fst) → motive (x.toUnion))
  (diffSnd: (x: HDiffElemAt T1 T2 .snd) → motive (x.toUnion))
  (inter: (x: HInterElemAt T1 T2) → motive x.toUnion)
  (t: HUnionElemAt T1 T2)
  : motive t :=
  if lm1: isInEmbedRangeAt T1 T2 t.val .fst then
    if lm2: isInEmbedRangeAt T1 T2 t.val .snd then
      inter (Subtype.mk t.val (hinterSetUnivAt_mem_iff_isInEmbedRangeAt.mpr (And.intro lm1 lm2)))
    else
      diffFst (Subtype.mk t.val (by
        simp at lm2;
        simp [isInEmbedRangeAt_eq_true_iff, EmbedRangeAt] at lm1
        simp [isInEmbedRangeAt_eq_false_iff, EmbedRangeAt] at lm2
        simp [hdiffSetUnivAt, hdiffSet]
        exact And.intro lm1 lm2 ))
  else if lm2: isInEmbedRangeAt T1 T2 t.val .snd then
    diffSnd (Subtype.mk t.val (by
        simp at lm1;
        simp [isInEmbedRangeAt_eq_false_iff, EmbedRangeAt] at lm1
        simp [isInEmbedRangeAt_eq_true_iff, EmbedRangeAt] at lm2
        simp [hdiffSetUnivAt, hdiffSet]
        exact And.intro lm2 lm1 ))
  else
    False.elim (by
      have lm3 := t.property
      rewrite [hunionSetUnivAt_mem_iff] at lm3
      simp [isInEmbedRangeAt_eq_false_iff, EmbedRangeAt] at lm1 lm2
      rcases lm3 with lm3 | lm3
      <;> rcases lm3 with ⟨lv, lm3⟩
      · exact lm1 lv lm3
      · exact lm2 lv lm3 )

@[elab_as_elim]
def recLiftDiffAt [DecidableEmbedRange T1 T2] (lb: Label)
  {motive: HUnionElemAt T1 T2 → Sort _}
  (lift: (x: EmbedElemAt T1 T2 lb) → motive (.ofEmbedElem x))
  (diff: (x: HDiffElemAt T1 T2 lb.toDual) → motive (.ofEmbedElem x.toEmbedElem))
  (t: HUnionElemAt T1 T2)
  : motive t :=
  if lm1: isInEmbedRangeAt T1 T2 t.val lb then
    lift (Subtype.mk t.val (by simpa [isInEmbedRangeAt_eq_true_iff] using lm1))
  else
    diff (Subtype.mk t.val (by
      simp [isInEmbedRangeAt_eq_false_iff] at lm1
      have lm2 := t.property
      rewrite [hunionSetUnivAt_mem_iff] at lm2
      cases lb <;> (
        simp [hdiffSetUnivAt, hdiffSet, Label.toDual]
        simp [EmbedRangeAt] at lm1
        simp [lm1]
        simp [lm1] at lm2
        exact lm2 )))

end HUnionElemAt


def hunionFinset [DecidableEq (R T1 T2)] (s1: Finset T1) (s2: Finset T2) : Finset (R T1 T2) := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))

def hunionFinsetUnivAt (T1 T2: Type u1) [HasHUnion T1 T2] [DecidableEq (R T1 T2)] [Fintype T1] [Fintype T2] : Finset (R T1 T2) := hunionFinset (Finset.univ: Finset T1) (Finset.univ: Finset T2)

theorem hunionFinsetUnivAt_eq_hunionSetUnivAt [DecidableEq (R T1 T2)] [Fintype T1] [Fintype T2]
  : ((hunionFinsetUnivAt T1 T2): Set (R T1 T2)) = hunionSetUnivAt T1 T2 := by
  dsimp [hunionFinsetUnivAt, hunionSetUnivAt, hunionSet, hunionFinset]
  simp


instance hunionFintypeAt (T1 T2: Type u1) [Fintype T1] [Fintype T2] [HasHUnion T1 T2] [DecidableEq (R T1 T2)] : Fintype (HUnionElemAt T1 T2) :=
  have lm2 := @hunionFinsetUnivAt_eq_hunionSetUnivAt T1 T2 _ _ _ _ |> Set.ext_iff.mp
  let embedding : (hunionFinsetUnivAt T1 T2) ↪ (hunionSetUnivAt T1 T2) :=
    {
      toFun x := Subtype.mk x.val (by
        rcases x with ⟨x, lm1⟩
        simp
        exact (lm2 x).mp lm1)
      inj' := by intro _ _; simp
    }
  let elems : Finset (hunionSetUnivAt T1 T2) := (hunionFinsetUnivAt T1 T2: Finset (R T1 T2)).attach.map embedding
  {
    elems := elems
    complete := by
      rintro ⟨x, lm1⟩
      subst elems
      subst embedding
      simp
      exact (lm2 x).mpr lm1
  }


theorem hunionFinset_dist [DecidableEq (R T1 T2)] {s1: Finset T1} {s2: Finset T2}
  : (hunionFinset s1 s2: Set (R T1 T2)) = (hunionSet (s1: Set T1) (s2: Set T2)) := by
  dsimp [hunionFinset, hunionSet]
  simp

instance (priority := low) [dec: (rv: R T1 T2) → Decidable (rv ∈ Set.range (HasHUnion.fst: T1 → (R T1 T2)))] rv : Decidable (rv ∈ EmbedRangeAt T1 T2 .fst) := dec rv

instance (priority := low) [dec: (rv: R T1 T2) → Decidable (rv ∈ Set.range (HasHUnion.snd: T2 → (R T1 T2)))] rv : Decidable (rv ∈ EmbedRangeAt T1 T2 .snd) := dec rv

instance ofFstSnd [decFst: ∀rv, Decidable (rv ∈ EmbedRangeAt T1 T2 .fst)] [decSnd: ∀rv, Decidable (rv ∈ EmbedRangeAt T1 T2 .snd)] lb rv : Decidable (rv ∈ EmbedRangeAt T1 T2 lb) :=
  lb.casesOn (fun rv => decFst rv) (fun rv => decSnd rv) <| rv


open DecidableEmbedRange in
def hunionIndicator [DecidableEmbedRange T1 T2] (s1: T1 → Bool) (s2: T2 → Bool) (rv: R T1 T2) : Bool :=
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
theorem hunionIndicator_eq_true_iff [DecidableEmbedRange T1 T2] {s1: T1 → Bool} {s2: T2 → Bool} {rv: R T1 T2}
  : (hunionIndicator s1 s2 rv = .true) ↔ ((∃req1, s1 (liftAt T1 T2 rv .fst req1) = .true) ∨ (∃req2, s2 (liftAt T1 T2 rv .snd req2) = .true)) := by
  cases lm1: isInEmbedRangeAt T1 T2 rv .fst
  <;> cases lm2: isInEmbedRangeAt T1 T2 rv .snd
  <;> simp [lm1, lm2, hunionIndicator]
  <;> (
    revert lm1 lm2
    simp [isInEmbedRangeAt_eq_true_iff, isInEmbedRangeAt_eq_false_iff]
    intro lm1 lm2
    simp [lm1, lm2] )


theorem hunionIndicator_set_eq [DecidableEmbedRange T1 T2] {s1: T1 → Bool} {s2: T2 → Bool}
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

/-
def restrict.{u3, u4}
  (DomL1 DomL2: Type u1) (DomR: Type u2) [HasHUnion DomL1 DomL2 DomR]
  (CodL1 CodL2: Type u3) (CodR: Type u4) [HasHUnion CodL1 CodL2 CodR]
  (f: DomL1 → CodL1) (x: HInterElemAt DomL1 DomL2 DomR) : HInterElemAt CodL1 CodL2 CodR :=
  Subtype.mk (embedAt CodL1 CodL2 .fst (f (x.liftAt .fst))) (by
    simp [hinterSetUnivAt_mem_iff]
    --exists (embedAt CodL1 CodL2 .fst (f (x.liftAt .fst)))
  )
-/

/-
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
-/



open DecidableEmbedRange in
@[elab_as_elim]
def recDiffInterAt [DecidableEmbedRange T1 T2] (lb: Label)
  {motive: LeftTypeAt T1 T2 lb → Sort _}
  (diff: (x: HDiffElemAt T1 T2 lb) → motive x.lift)
  (inter: (x: HInterElemAt T1 T2) → motive (x.liftAt lb))
  (t: LeftTypeAt T1 T2 lb)
  : motive t :=
  let et : EmbedElemAt T1 T2 lb := .pureAt _ _ _ t
  if lm1: isInEmbedRangeAt T1 T2 et.val lb.toDual then
    inter (Subtype.mk et.val (by
      subst et
      dsimp [EmbedElemAt.pureAt] at lm1 ⊢
      rw [isInEmbedRangeAt_eq_true_iff] at lm1
      rw [hinterSetUnivAt_mem_iff_embedRangeAt_mem]
      intro lb2
      cases lb <;> cases lb2
      · simp
      · dsimp [Label.toDual] at lm1; exact lm1
      · dsimp [Label.toDual] at lm1; exact lm1
      · simp ))
    |> Eq.subst (by
      subst et
      dsimp [EmbedElemAt.pureAt, HInterElemAt.liftAt]
      rw [embedAt_liftAt_eq] )
  else
    diff (Subtype.mk et.val (by
      subst et
      dsimp [EmbedElemAt.pureAt] at lm1 ⊢
      rw [Bool.not_eq_true, isInEmbedRangeAt_eq_false_iff] at lm1
      rw [hdiffSetUnivAt_mem_iff_embedRangAt_mem]
      simp [lm1] ))
    |> Eq.subst (by
      subst et
      dsimp [EmbedElemAt.pureAt, HDiffElemAt.lift]
      rw [embedAt_liftAt_eq] )


class Bundle (T1 T2: Type u1) where
  hasHUnion: HasHUnion.{u1, u2} T1 T2
  memDecidable : DecidableEmbedRange.{u1, u2} T1 T2


attribute [reducible, instance] Bundle.hasHUnion Bundle.memDecidable


namespace Bundle

open LiftableEmbedding

@[reducible]
def ofRefl (T: Type*) : Bundle T T :=
  let hu := HasHUnion.ofRefl T
  {
    hasHUnion := hu
    memDecidable := @ofFstSnd T T _ (decidableRangeMemOfRefl T) (decidableRangeMemOfRefl T)
  }

@[reducible]
def ofSum (L1 L2: Type u1) : Bundle L1 L2 :=
  let hu := HasHUnion.ofSum L1 L2
  {
    hasHUnion := hu
    memDecidable := @ofFstSnd L1 L2 _ (decidableRangeMemOfSumLeft L1 L2) (decidableRangeMemOfSumRight L1 L2)
  }



end Bundle

end HasHUnion


end Nemonuri

end
