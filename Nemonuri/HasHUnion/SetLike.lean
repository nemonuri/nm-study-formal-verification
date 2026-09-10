module

public import Nemonuri.HasHUnion.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.HasHUnion

section EmbedSetAt

universe u1 u2
variable {L1 L2: Type u1} [HasHUnion.{u1, u2} L1 L2]

def RightSet (L1 L2: Type u1) [HasHUnion.{u1, u2} L1 L2] : Type _ := Set (R L1 L2)

def embedSetAt (lb: Label) (s: Set (LeftTypeAt L1 L2 lb)) : RightSet L1 L2 := s.image (embedAt L1 L2 lb)

theorem embedSetAt_injective {lb: Label} : Function.Injective (embedSetAt lb: Set (LeftTypeAt L1 L2 lb) → RightSet L1 L2) := by
  intro s1 s2 lm1
  dsimp [embedSetAt, RightSet] at lm1
  simp [Set.ext_iff] at lm1 ⊢
  intro lv
  specialize lm1 (embedAt L1 L2 lb lv)
  simp [embedAt_injective.eq_iff] at lm1
  exact lm1

theorem embedSetAt_injective_at (lb: Label) : Function.Injective (embedSetAt lb: Set (LeftTypeAt L1 L2 lb) → RightSet L1 L2) := embedSetAt_injective

namespace RightSet

def ofSet (s: Set (R L1 L2)) : RightSet L1 L2 := s

def toSet (rs: RightSet L1 L2) : Set (R L1 L2) := rs

instance toUnion : Union (RightSet L1 L2) where
  union rs1 rs2 := ofSet (rs1.toSet ∪ rs2.toSet)

@[defeq]
theorem union_def {rs1 rs2: RightSet L1 L2} : (rs1 ∪ rs2) = ofSet (rs1.toSet ∪ rs2.toSet) := rfl

instance toMembership : Membership (R L1 L2) (RightSet L1 L2) where
  mem rs re := re ∈ rs.toSet

@[defeq]
theorem mem_def {rs: RightSet L1 L2} {re: R L1 L2} : (re ∈ rs) = (re ∈ rs.toSet) := rfl

end RightSet

end EmbedSetAt

universe u1 u2 u3
variable {LS1 LS2: Type u1} {L1 L2: Type u2} [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2]

namespace RightSet

def ofSetLikeHUnion (ls1: LS1) (ls2: LS2) : RightSet L1 L2 := (embedSetAt .fst (ls1: Set L1)) ∪ (embedSetAt .snd (ls2: Set L2))

structure SetLikeHUnionMemDecidableProd (LS1 LS2: Type u1) (L1 L2: Type u2) [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2] where
  fst: LS1
  snd: LS2
  toDecidableMem (elemR: R L1 L2) : Decidable (elemR ∈ ofSetLikeHUnion fst snd)


namespace SetLikeHUnionMemDecidableProd

variable [DecidableEmbedRange L1 L2]

open DecidableEmbedRange

def decideMem (ls1: LS1) (ls2: LS2) [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] (er: R L1 L2) : Bool := --Decidable (er ∈ ofSetLikeHUnion ls1 ls2)
  let loc1 (_: Unit) : Bool :=
    if lm1_1: isInEmbedRangeAt L1 L2 er .snd = .true then
      let lv : L2 := liftAt L1 L2 er .snd (isInEmbedRangeAt_eq_true_iff.mp lm1_1)
      decide (lv ∈ ls2)
    else
      .false
  if lm1: isInEmbedRangeAt L1 L2 er .fst = .true then
    let lv : L1 := liftAt L1 L2 er .fst (isInEmbedRangeAt_eq_true_iff.mp lm1)
    if decide (lv ∈ ls1) = .true then .true else loc1 ()
  else
    loc1 ()

theorem decideMem_iff_ofSetLikeHUnion_mem {ls1: LS1} {ls2: LS2} [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] {er: R L1 L2}
  : (decideMem ls1 ls2 er = .true) ↔ (er ∈ ofSetLikeHUnion ls1 ls2) := by
  dsimp [ofSetLikeHUnion, union_def, toSet, ofSet, mem_def]
  simp [embedSetAt]
  constructor
  · intro lm1
    simp [decideMem] at lm1
    by_cases lm2: isInEmbedRangeAt L1 L2 er .fst = .true
    · simp [lm2] at lm1
      obtain ⟨lv, lm3⟩ := isInEmbedRangeAt_eq_true_iff.mp lm2 |> EmbedRangeAt.exists_embedAt_iff.mp
      rewrite [Eq.comm] at lm3
      subst lm3
      simp [embedAt_liftAt_eq] at lm1
      rcases lm1 with lm1 | lm1
      · refine Or.inl ?_
        exists lv
      · refine Or.inr ?_
        rcases lm1 with ⟨lm1, lm3⟩
        obtain ⟨lv2, lm4⟩ := isInEmbedRangeAt_eq_true_iff.mp lm1 |> EmbedRangeAt.exists_embedAt_iff.mp
        exists lv2
        simp [lm4]
        simp [← lm4, embedAt_liftAt_eq] at lm3
        exact lm3
    · simp at lm2
      simp [lm2] at lm1
      rcases lm1 with ⟨lm1, lm3⟩
      obtain ⟨lv2, lm4⟩ := isInEmbedRangeAt_eq_true_iff.mp lm1 |> EmbedRangeAt.exists_embedAt_iff.mp
      refine Or.inr ?_
      rewrite [Eq.comm] at lm4
      subst lm4
      simp [embedAt_liftAt_eq] at lm3
      exists lv2
  · intro lm1
    rcases lm1 with lm1 | lm1 <;> (rcases lm1 with ⟨lv, lm1, lm2⟩)
    · rewrite [Eq.comm] at lm2
      subst lm2
      simp [decideMem, isInEmbedRangeAt_eq_true_iff, embedAt_liftAt_eq]
      exact Or.inl lm1
    · rewrite [Eq.comm] at lm2
      subst lm2
      simp [decideMem, isInEmbedRangeAt_eq_true_iff, embedAt_liftAt_eq, lm1]


def ofDecidableMem (ls1: LS1) (ls2: LS2) [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] : SetLikeHUnionMemDecidableProd LS1 LS2 L1 L2 where
  fst := ls1
  snd := ls2
  toDecidableMem er := decidable_of_iff (decideMem ls1 ls2 er = .true) decideMem_iff_ofSetLikeHUnion_mem




end SetLikeHUnionMemDecidableProd

end RightSet

--def RightSet : Type _ := Set (R L1 L2)

/-
def SetOfSetLikeHUnion (ls1: LS1) (ls2: LS2) : Set (R L1 L2) := (embedSetAt .fst (ls1: Set L1)) ∪ (embedSetAt .snd (ls2: Set L2))

structure UnionMemDecidableProd (LS1 LS2: Type u1) (L1 L2: Type u2) [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2] where
  fst: LS1
  snd: LS2
  toDecidableUnionMem (elemR: R L1 L2) : Decidable (elemR ∈ SetOfSetLikeHUnion fst snd)
-/



end Nemonuri.HasHUnion

end
