module

public import Nemonuri.TransitionSystemLike.Basic
public import Nemonuri.HasHUnion

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 38

-/

@[expose] public section

namespace Nemonuri.TransitionSystem

universe us1 us2 uact_l uap_l uact_r uap_r


structure Interleaving (Act: Type uact_r) (AP: Type uap_r) (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) where
  actHasHUnionBundle: HasHUnion.Bundle ts1.Act ts2.Act Act
  apHasHUnionBundle: HasHUnion.Bundle ts1.AP ts2.AP AP

--attribute [reducible, instance] Interleaving.actHasHUnionBundle Interleaving.apHasHUnionBundle

namespace Interleaving

open HasHUnion

variable {Act: Type uact_r} {AP: Type uap_r} {ts1: TransitionSystem.{us1, uact_l, uap_l}} {ts2: TransitionSystem.{us2, uact_l, uap_l}}


@[reducible]
def toActHasHUnion (il: Interleaving Act AP ts1 ts2) : HasHUnion ts1.Act ts2.Act Act := il.actHasHUnionBundle.hasHUnion

def toActMemDecidable (il: Interleaving Act AP ts1 ts2) (lb: Label) (rv: Act)
  : letI := il.toActHasHUnion; Decidable (rv ∈ EmbedRangeAt ts1.Act ts2.Act lb) := il.actHasHUnionBundle.memDecidable lb rv

@[reducible]
def toAPHasHUnion (il: Interleaving Act AP ts1 ts2) : HasHUnion ts1.AP ts2.AP AP := il.apHasHUnionBundle.hasHUnion

def toAPMemDecidable (il: Interleaving Act AP ts1 ts2) (lb: Label) (rv: AP)
  : letI := il.toAPHasHUnion; Decidable (rv ∈ EmbedRangeAt ts1.AP ts2.AP lb) := il.apHasHUnionBundle.memDecidable lb rv


abbrev LeftActTypeAt (il: Interleaving Act AP ts1 ts2) (lb: Label) : Type uact_l := il.toActHasHUnion.LeftTypeAt ts1.Act ts2.Act Act lb

def embedAt (il: Interleaving Act AP ts1 ts2) (lb: Label) (lv: il.LeftActTypeAt lb) : Act := il.toActHasHUnion.embedAt ts1.Act ts2.Act lb lv



@[mk_iff]
inductive Transition (il: Interleaving Act AP ts1 ts2) : ts1.S → ts2.S → Act → ts1.S → ts2.S → Prop where
  | fst (s₁1: ts1.S) (a₁: ts1.Act) (s₁2: ts1.S) (req: s₁1 ─⌞a₁⌟→{ts1} s₁2) (s₂: ts2.S) : Transition il s₁1 s₂ (il.embedAt .fst a₁) s₁2 s₂
  | snd (s₂1: ts2.S) (a₂: ts2.Act) (s₂2: ts2.S) (req: s₂1 ─⌞a₂⌟→{ts2} s₂2) (s₁: ts1.S) : Transition il s₁ s₂1 (il.embedAt .snd a₂) s₁ s₂2

@[reducible]
def toTransitionSystem (il: Interleaving Act AP ts1 ts2) : TransitionSystem where
  S := ts1.S × ts2.S
  Act := il.toActHasHUnion.hunionSetUnivAt _ _
  I := Set.prod ts1.I ts2.I
  AP := il.toAPHasHUnion.hunionSetUnivAt _ _
  L s ap := letI := il.toAPMemDecidable; il.toAPHasHUnion.hunionIndicator (ts1.labeling s.fst) (ts2.labeling s.snd) ap.val
  tr s1 a s2 := Transition il s1.fst s1.snd a s2.fst s2.snd



/-
theorem toTransitionSystem_injective : Function.Injective (@toTransitionSystem Act AP ts1 ts2) := by
  intro x1 x2
  simp [toTransitionSystem]
  intro lm1 lm2 lm3 lm4
-/
  --rintro ⟨⟨_,_⟩, ⟨_,_⟩⟩ ⟨⟨_,_⟩, ⟨_,_⟩⟩
  --simp [Set.Elem, hunionSet] at lm1
  --rewrite [lm1] at lm5
  --intro lm1 lm2 lm3 lm4
  ---dsimp [Set.Elem] at lm1

/-
theorem toTransitionSystem_injective : Function.Injective (@toTransitionSystem Act AP ts1 ts2) := by
  rintro ⟨ac1_1, ap1_1, ac2_1, ap2_1, lb1, lm_lb1⟩
  rintro ⟨ac1_2, ap1_2, ac2_2, ap2_2, lb2, lm_lb2⟩
  simp [toTransitionSystem]
  intro lm1 lm2 lm3 lm4
  simp [Set.Elem] at lm1 lm2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Function.Embedding.ext ?_
    intro act1
    revert lm2
    simp [heq_iff_exists_cast_eq]
    intro lm2_1 lm2_2
    simp [funext_iff, transition_iff] at lm2_2
    have lm5 := ac1_1.injective.leftInverse
-/
/-
    dsimp [TransitionSystem.labeling] at lm_lb1
    have (eq := lm5) T1 := { x // (∃ y, ac1_1 y = x) ∨ ∃ y, ac2_1 y = x }
    have (eq := lm6) t1 : T1 := cast lm5.symm ⟨ac1_1 act1, by simp⟩
-/
    --have lm7 := lm5.trans lm1
    --subst lm7




end Interleaving


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
