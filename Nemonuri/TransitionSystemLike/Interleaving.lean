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




structure Interleaving (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) where
  act: BiUniqueIndicator ts1.Act ts2.Act
  ap: BiUniqueIndicator ts1.AP ts2.AP


namespace Interleaving



variable {ts1: TransitionSystem.{us1, uact_l, uap_l}} {ts2: TransitionSystem.{us2, uact_l, uap_l}}



inductive Transition (il: Interleaving ts1 ts2) : ts1.S → ts2.S → SumUnion il.act.Rel → ts1.S → ts2.S → Prop where
  | fst (s₁1: ts1.S) (a₁: ts1.Act) (s₁2: ts1.S) (req: s₁1 ─⌞a₁⌟→{ts1} s₁2) (s₂: ts2.S) : Transition il s₁1 s₂ (.ofSum (.inl a₁)) s₁2 s₂
  | snd (s₂1: ts2.S) (a₂: ts2.Act) (s₂2: ts2.S) (req: s₂1 ─⌞a₂⌟→{ts2} s₂2) (s₁: ts1.S) : Transition il s₁ s₂1 (.ofSum (.inr a₂)) s₁ s₂2


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


section Labeling

variable {il: Interleaving ts1 ts2} {s1: ts1.S} {s2: ts2.S} [HasPartialCongruence il.ap.Rel]

theorem labelingCongruenceOfLeft_eq_true_iff {l: ts1.AP} : (il.labelingCongruenceOfLeft s2 l = .true) ↔ (∃r, il.ap.Rel l r ∧ ts2.labeling s2 r = .true) := by
  let hpc : HasPartialCongruence il.ap.Rel := inferInstance
  dsimp [labelingCongruenceOfLeft, PartialCongruence.ofRel]
  split
  · rename_i r lm1
    replace lm1 := hpc.partialCongruence.valid.rel_of_right?_eq_some lm1
    constructor
    · intro lm2
      exists r
    · rintro ⟨r2, lm2, lm3⟩
      have lm4 := IsBiUnique.rightUnique lm1 lm2
      rw [lm4]
      exact lm3
  · rename_i lm1
    replace lm1 := hpc.partialCongruence.valid.right?_eq_none_iff_forall_not_rel.mp lm1
    simp
    intro r lm2
    specialize lm1 r
    contradiction

theorem labelingCongruenceOfRight_eq_true_iff {r: ts2.AP} : (il.labelingCongruenceOfRight s1 r = .true) ↔ (∃l, il.ap.Rel l r ∧ ts1.labeling s1 l = .true) := by
  let hpc : HasPartialCongruence il.ap.Rel := inferInstance
  dsimp [labelingCongruenceOfRight, PartialCongruence.ofRel]
  split
  · rename_i l lm1
    replace lm1 := hpc.partialCongruence.valid.rel_of_left?_eq_some lm1
    constructor
    · intro lm2
      exists l
    · rintro ⟨l2, lm2, lm3⟩
      have lm4 := IsBiUnique.leftUnique lm1 lm2
      rw [lm4]
      exact lm3
  · rename_i lm1
    replace lm1 := hpc.partialCongruence.valid.left?_eq_none_iff_forall_not_rel.mp lm1
    simp
    intro l lm2
    specialize lm1 l
    contradiction


end Labeling



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


theorem labelingRange_mem_iff_labeling_eq_true {il: Interleaving ts1 ts2} {s1: ts1.S} {s2: ts2.S} [HasPartialCongruence il.ap.Rel] {ap: SumUnion il.ap.Rel}
  : ap ∈ il.labelingRange s1 s2 ↔ il.labeling s1 s2 ap := by
  let hpc : HasPartialCongruence il.ap.Rel := inferInstance
  have lm_hpc := hpc.partialCongruence.valid
  cases ap using SumUnion.indOfSum
  rename_i aps
  rcases aps with ⟨apL⟩ | ⟨apR⟩
  <;> (
    simp [labelingRange, SumUnion.ofSum_eq_iff_sumEquivGen, sumEquivGen_iff]
    dsimp [labeling, SumUnion.liftOfSum_ofSum, labelingSum] )
  · by_cases lm1: ts1.labeling s1 apL = .true
    · simp [lm1]
    · simp [lm1]
      dsimp [labelingCongruenceOfLeft, PartialCongruence.ofRel]
      split
      · rename_i apR lm2
        replace lm2 := lm_hpc.rel_of_right?_eq_some lm2
        constructor
        · rintro ⟨apR2, lm3, lm4⟩
          have lm5 := IsBiUnique.rightUnique lm2 lm3
          rw [lm5]
          exact lm4
        · rintro lm3
          exists apR
      · rename_i lm2
        simp
        intro apR lm3
        replace lm2 := lm_hpc.right?_eq_none_iff_forall_not_rel.mp lm2 apR
        contradiction
  · by_cases lm1: ts2.labeling s2 apR = .true
    · simp [lm1]
    · simp [lm1]
      dsimp [labelingCongruenceOfRight, PartialCongruence.ofRel]
      split
      · rename_i apL lm2
        replace lm2 := lm_hpc.rel_of_left?_eq_some lm2
        constructor
        · rintro ⟨apL2, lm3, lm4⟩
          have lm5 := IsBiUnique.leftUnique lm2 lm3
          rw [lm5]
          exact lm4
        · rintro lm3
          exists apL
      · rename_i lm2
        simp
        intro apL lm3
        replace lm2 := lm_hpc.left?_eq_none_iff_forall_not_rel.mp lm2 apL
        contradiction

@[reducible]
def toTransitionSystem (il: Interleaving ts1 ts2) [HasPartialCongruence il.ap.Rel] : TransitionSystem where
  S := ts1.S × ts2.S
  Act := SumUnion il.act.Rel
  I := Set.prod ts1.I ts2.I
  AP := SumUnion il.ap.Rel
  L s := il.labeling s.fst s.snd
  tr s1 ap s2 := il.Transition s1.fst s1.snd ap s2.fst s2.snd

@[reducible]
noncomputable def toTransitionSystemOfClassical (il: Interleaving ts1 ts2) : TransitionSystem :=
  letI := HasPartialCongruence.ofClassical il.ap.Rel
  il.toTransitionSystem

/-
structure Interleaving (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) where
  act: BiUniqueIndicator ts1.Act ts2.Act --HasHUnion.Bundle.{uact_l, uact_r} ts1.Act ts2.Act
  ap: BiUniqueIndicator ts1.AP ts2.AP --HasHUnion.Bundle.{uap_l, uap_r} ts1.AP ts2.AP
-/

end Interleaving




end Nemonuri.TransitionSystem

end
