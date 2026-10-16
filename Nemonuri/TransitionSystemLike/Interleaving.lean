module

public import Nemonuri.TransitionSystemLike.Basic
public import Nemonuri.Relations.Heterogeneous.SumRelGen

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 38

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

open Nemonuri.Relations.Heterogeneous

universe us1 us2 uact_l uap_l uact_r uap_r

/-
class HasInterleaving (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) (Act: outParam <| Type uact_r) (AP: outParam <| Type uap_r) where
  act : HasHUnion.Bundle ts1.Act ts2.Act Act
  ap : HasHUnion.Bundle ts1.AP ts2.AP AP
-/

--attribute [reducible, instance] HasInterleaving.act HasInterleaving.ap


structure Interleaving (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) where
  act: BiUniqueIndicator ts1.Act ts2.Act --HasHUnion.Bundle.{uact_l, uact_r} ts1.Act ts2.Act
  ap: BiUniqueIndicator ts1.AP ts2.AP --HasHUnion.Bundle.{uap_l, uap_r} ts1.AP ts2.AP
  --ap_valid (ap1: ts1.AP) (ap2: ts2.AP) (req: ap.Rel ap1 ap2) (s1: ts1.S) (s2: ts2.S) : ts1.labeling s1 ap1 = ts2.labeling s2 ap2


--attribute [reducible, instance] Interleaving.actHasHUnionBundle Interleaving.apHasHUnionBundle

namespace Interleaving

--open HasHUnion

variable {ts1: TransitionSystem.{us1, uact_l, uap_l}} {ts2: TransitionSystem.{us2, uact_l, uap_l}} --{Act: Type uact_r} {AP: Type uap_r}


--abbrev inferAt (Act AP: Type _) [i: HasInterleaving ts1 ts2 Act AP] : HasInterleaving ts1 ts2 Act AP := i

--abbrev LeftActTypeAt (il: Interleaving ts1 ts2) (lb: Label) : Type _ := il.act.hasHUnion.LeftTypeAt ts1.Act ts2.Act lb

--def embedActAt (il: Interleaving ts1 ts2) (lb: Label) (lv: il.LeftActTypeAt lb) : il.act.hasHUnion.R := il.act.hasHUnion.embedAt ts1.Act ts2.Act lb lv

--def embedActAt (Act AP: Type _) [HasInterleaving ts1 ts2 Act AP] (lb: Label) (lv: LeftActTypeAt Act AP lb) : Act := il.toActHasHUnion.embedAt ts1.Act ts2.Act lb lv

inductive Transition (il: Interleaving ts1 ts2) : ts1.S → ts2.S → SumUnion il.act.Rel → ts1.S → ts2.S → Prop where
  | fst (s₁1: ts1.S) (a₁: ts1.Act) (s₁2: ts1.S) (req: s₁1 ─⌞a₁⌟→{ts1} s₁2) (s₂: ts2.S) : Transition il s₁1 s₂ (.ofSum (.inl a₁)) s₁2 s₂
  | snd (s₂1: ts2.S) (a₂: ts2.Act) (s₂2: ts2.S) (req: s₂1 ─⌞a₂⌟→{ts2} s₂2) (s₁: ts1.S) : Transition il s₁ s₂1 (.ofSum (.inr a₂)) s₁ s₂2

-- (ap: SumUnion il.ap.Rel)
-- (il: Interleaving ts1 ts2)

def labelingRange (il: Interleaving ts1 ts2) (s1: ts1.S) (s2: ts2.S) : Set (SumUnion il.ap.Rel) :=
  { ap: SumUnion il.ap.Rel | ∃(ap1: ts1.AP), ap = .ofSum (.inl ap1) ∧ ts1.labeling s1 ap1 = .true } ∪
  { ap: SumUnion il.ap.Rel | ∃(ap2: ts2.AP), ap = .ofSum (.inr ap2) ∧ ts2.labeling s2 ap2 = .true }


def labelingCongruenceOfLeft (il: Interleaving ts1 ts2) (s2: ts2.S) [HasPartialCongruence il.ap.Rel] (l: ts1.AP) : Bool :=
  match (PartialCongruence.ofRel il.ap.Rel).right? l with
  | .some r => ts2.labeling s2 r
  | .none => .false

def labelingCongruenceOfRight (il: Interleaving ts1 ts2) (s1: ts1.S) [HasPartialCongruence il.ap.Rel] (r: ts2.AP) : Bool :=
  match (PartialCongruence.ofRel il.ap.Rel).left? r with
  | .some l => ts1.labeling s1 l
  | .none => .false


def labelingSum (il: Interleaving ts1 ts2) (s1: ts1.S) (s2: ts2.S) [HasPartialCongruence il.ap.Rel] : (ts1.AP ⊕ ts2.AP) → Bool
  | .inl ap => (ts1.labeling s1 ap) || il.labelingCongruenceOfLeft s2 ap
  | .inr ap => (ts2.labeling s2 ap) || il.labelingCongruenceOfRight s1 ap

def labeling (il: Interleaving ts1 ts2) (s1: ts1.S) (s2: ts2.S) [HasPartialCongruence il.ap.Rel] (ap: SumUnion il.ap.Rel) : Bool :=
  ap.liftOfSum (labelingSum il s1 s2 ·) (by
    let hpc : HasPartialCongruence il.ap.Rel := inferInstance
    have lm_hpc := hpc.partialCongruence.valid
    intro aps1 aps2 lm1
    replace lm1 := lm1.eq_or_rel_exists IsBiUnique.biUnique
    rcases aps1 with ⟨apL1⟩ | ⟨apR1⟩
    <;> rcases aps2 with ⟨apL2⟩ | ⟨apR2⟩
    <;> (simp at lm1 ⊢)
    · subst lm1; rfl
    · dsimp [labelingSum]
      refine Bool.eq_iff_iff.mpr ?_
      simp [labelingCongruenceOfLeft, PartialCongruence.ofRel]
      split
      · rename_i apR1 lm2
        replace lm2 := lm_hpc.rel_of_right?_eq_some lm2
        have lm3 := IsBiUnique.rightUnique lm1 lm2
        subst lm3
        by_cases lm3: ts2.labeling s2 apR2 = .true
        · simp [lm3]
        · simp [lm3]
          simp [labelingCongruenceOfRight, PartialCongruence.ofRel]
          split
          · rename_i apL2 lm4
            replace lm3 := lm_hpc.rel_of_left?_eq_some lm4
            have lm5 := IsBiUnique.leftUnique lm1 lm3
            rw [lm5]
          · rename_i lm4
            replace lm4 := lm_hpc.left?_eq_none_iff_forall_not_rel.mp lm4 apL1
            contradiction
      · rename_i lm4
        replace lm4 := lm_hpc.right?_eq_none_iff_forall_not_rel.mp lm4 apR2
        contradiction
    · dsimp [labelingSum]
      refine Bool.eq_iff_iff.mpr ?_
      simp [labelingCongruenceOfRight, PartialCongruence.ofRel]
      split
      · rename_i apL1 lm2
        replace lm2 := lm_hpc.rel_of_left?_eq_some lm2
        have lm3 := IsBiUnique.leftUnique lm1 lm2
        subst lm3
        by_cases lm3: ts1.labeling s1 apL2 = .true
        · simp [lm3]
        · simp [lm3]
          simp [labelingCongruenceOfLeft, PartialCongruence.ofRel]
          split
          · rename_i apR2 lm4
            replace lm3 := lm_hpc.rel_of_right?_eq_some lm4
            have lm5 := IsBiUnique.rightUnique lm1 lm3
            rw [lm5]
          · rename_i lm4
            replace lm4 := lm_hpc.right?_eq_none_iff_forall_not_rel.mp lm4 apR1
            contradiction
      · rename_i lm4
        replace lm4 := lm_hpc.left?_eq_none_iff_forall_not_rel.mp lm4 apL2
        contradiction
    · subst lm1; rfl )

/-
theorem labelingRange_mem_iff_labeling_eq_true {il: Interleaving ts1 ts2} {s1: ts1.S} {s2: ts2.S} [HasPartialCongruence il.ap.Rel] {ap: SumUnion il.ap.Rel}
  : ap ∈ il.labelingRange s1 s2 ↔ il.labeling s1 s2 ap := by
  cases ap using SumUnion.indOfSum
  rename_i aps
  rcases aps with ⟨apL⟩ | ⟨apR⟩
  <;> (
    simp [labelingRange, SumUnion.ofSum_eq_iff_sumEquivGen, sumEquivGen_iff]
    dsimp [labeling, SumUnion.liftOfSum_ofSum, labelingSum] )
  · by_cases lm1: ts1.labeling s1 apL = .true
    · simp [lm1]
    · simp [lm1]
-/

/-
theorem labelingRange_mem_iff {il: Interleaving ts1 ts2} {s1: ts1.S} {s2: ts2.S} {ap: SumUnion il.ap.Rel} [HasPartialCongruence il.ap.Rel]
  : (ap ∈ il.labelingRange s1 s2) ↔ (∃aps, ap = .ofSum aps ∧ il.labelingSum s1 s2 aps) := by
  constructor
  · cases ap using SumUnion.indOfSum
    rename_i aps
    rcases aps with ⟨apL⟩ | ⟨apR⟩
    <;> (simp [labelingRange, SumUnion.ofSum_eq_iff_sumEquivGen, sumEquivGen_iff, labelingSum])
    · intro lm1
      rcases lm1 with lm1 | lm1
      · simp [lm1]
      · rcases lm1 with ⟨apR, lm1, lm2⟩
        right
        exists apR
        refine ⟨lm1, ?_⟩
        left
        exact lm2
    · intro lm1
      rcases lm1 with lm1 | lm1
      · rcases lm1 with ⟨apL, lm1, lm2⟩
        right
        exists apL
        refine ⟨lm1, ?_⟩
        left
        exact lm2
      · left
        left
        exact lm1
  ·
-/
    --simp [labelingRange]
/-
    intro lm1
    simp [labelingRange] at lm1
    cases ap using SumUnion.indOfSum
    rename_i aps
    rcases aps with ⟨apL⟩ | ⟨apR⟩
    <;> (simp at lm1 ⊢)
-/

/-
  cases ap using SumUnion.indOfSum
  rename_i s
  dsimp [labelingImage]
  simp [SumUnion.ofSum_eq_iff_sumEquivGen, sumEquivGen_iff]
  rcases s with ⟨l⟩ | ⟨r⟩ <;> simp
  ·
-/

--def labelingUnion (s1: ts1.S) (s2: ts2.S) : ts1.AP → ts2.AP → Bool
  --| .inl ap => ts1.labeling s1 ap
  --| .inr ap => ts2.labeling s2 ap

/-
def labeling (il: Interleaving ts1 ts2) (s1: ts1.S) (s2: ts2.S) (ap: SumUnion il.ap.Rel) : Bool :=
  ap.liftOfSum (labelingSum s1 s2 ·) (by
    intro ap1 ap2 lm1
    rewrite [sumEquivGen_iff] at lm1
    rcases lm1 with lm1 | lm1
    · subst lm1; rfl
    · rcases lm1 with ⟨apL, apR, lm1, lm2⟩
      rcases lm2 with ⟨lm2, lm3⟩ | ⟨lm2, lm3⟩
      <;> (subst lm2 lm3; dsimp [labelingSum])
      ·
  )
-/

/-
@[mk_iff]
inductive Transition (il: Interleaving ts1 ts2) : ts1.S → ts2.S → il.act.hasHUnion.R → ts1.S → ts2.S → Prop where
  | fst (s₁1: ts1.S) (a₁: ts1.Act) (s₁2: ts1.S) (req: s₁1 ─⌞a₁⌟→{ts1} s₁2) (s₂: ts2.S) : Transition il s₁1 s₂ (il.embedActAt .fst a₁) s₁2 s₂
  | snd (s₂1: ts2.S) (a₂: ts2.Act) (s₂2: ts2.S) (req: s₂1 ─⌞a₂⌟→{ts2} s₂2) (s₁: ts1.S) : Transition il s₁ s₂1 (il.embedActAt .snd a₂) s₁ s₂2
-/

/-
@[reducible]
def toTransitionSystem (il: Interleaving ts1 ts2) : TransitionSystem where
  S := ts1.S × ts2.S
  Act := letI := il.act.hasHUnion; HUnionElemAt ts1.Act ts2.Act
  I := Set.prod ts1.I ts2.I
  AP := letI := il.ap.hasHUnion; HUnionElemAt ts1.AP ts2.AP
  L s ap := letI := il.ap.memDecidable; il.ap.hasHUnion.hunionIndicator (ts1.labeling s.fst) (ts2.labeling s.snd) ap.val
  tr s1 a s2 := Transition il s1.fst s1.snd a s2.fst s2.snd

def toTransitionSystemActAP (il: Interleaving ts1 ts2) : TransitionSystem.OfActAP il.toTransitionSystem.Act il.toTransitionSystem.AP := il.toTransitionSystem.toActAP

def inferAt
  (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l})
  [HasHUnion.Bundle ts1.Act ts2.Act] [HasHUnion.Bundle ts1.AP ts2.AP]
  : Interleaving ts1 ts2 :=
  .mk inferInstance inferInstance

end Interleaving

def interleaveAt
  (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l})
  [HasHUnion.Bundle ts1.Act ts2.Act] [HasHUnion.Bundle ts1.AP ts2.AP]
  : TransitionSystem :=
  (Interleaving.inferAt ts1 ts2).toTransitionSystem
-/

section InterleaveAt

open HasHUnion

--variable {ts1: TransitionSystem.{us1, uact_l, uap_l}} {ts2: TransitionSystem.{us2, uact_l, uap_l}} {Act: Type uact_l} {AP: Type uap_l}
--         [hbAct0: HasHUnion.Bundle ts1.Act ts2.Act Act] [hbAP0: HasHUnion.Bundle ts1.AP ts2.AP AP]
--         [hbAct: HasHUnion.Bundle ts1.Act Act Act] [hbAP: HasHUnion.Bundle ts1.AP AP AP]

/-
instance [HasHUnion.Bundle ts1.Act ts2.Act Act] [HasHUnion.Bundle ts1.AP ts2.AP AP] [HasHUnion.Bundle ts1.Act Act Act]
  : HasHUnion ts1.Act (interleaveAt Act AP ts1 ts2).Act Act where
  fst := hbAct.hasHUnion.fst
-/
/-

  snd :=
    let embed : (interleaveAt Act AP ts1 ts2).Act ↪ Act := .mk (Subtype.val) Subtype.val_injective
    {
      toEmbedding := embed
      lift rv req := Subtype.mk rv (by
          simp [hunionSetUnivAt_mem_iff] at req ⊢
          dsimp [embedAt, toLiftableEmbeddingAt]

        )
      lift_valid := _
    }
-/

/-
instance [HasHUnion.Bundle ts1.Act ts2.Act Act] [HasHUnion.Bundle ts1.AP ts2.AP AP] : HasHUnion.Bundle ts1.Act ((interleaveAt Act AP ts1 ts2).Act) Act where
  hasHUnion :=
-/

end InterleaveAt

/-
open Interleaving in
def interleave
  {ActL1 ActL2: Type uact_l} {APL1 APL2: Type uap_l} {ActR: Type uact_r} {APR: Type uap_r}
  (ts1: TransitionSystem.OfActAP ActL1 APL1) (ts2: TransitionSystem.OfActAP ActL2 APL2)
-/
/-
  (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l})
  [HasHUnion.Bundle ts1.Act ts2.Act Act] [HasHUnion.Bundle ts1.AP ts2.AP AP]
  : TransitionSystem.OfActAP (inferAt ts1 ts2 Act AP).toTransitionSystem.Act (inferAt ts1 ts2 Act AP).toTransitionSystem.AP :=
  (inferAt ts1 ts2 Act AP).toTransitionSystem.toActAP
-/

/-
@[reducible]
def interleaving (ts1 ts2: TransitionSystem) : TransitionSystem where
  S := ts1.S × ts2.S
  Act := ts1.Act ⊕ ts2.Act
  I := Set.prod ts1.I ts2.I
  AP := ts1.AP ⊕ ts2.AP
-/


end Nemonuri.TransitionSystem

end
