module

public import Nemonuri.TransitionSystemLike.Basic

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 38

-/

@[expose] public section

namespace Nemonuri.TransitionSystem

structure Interleaving (Act AP: Type _) (ts1 ts2: TransitionSystem) where
  toAct1 : ts1.Act ↪ Act
  toAP1 : ts1.AP ↪ AP
  toAct2 : ts2.Act ↪ Act
  toAP2 : ts2.AP ↪ AP
  labeling (s1: ts1.S) (s2: ts2.S) : AP → Bool
  labeling_valid (s1: ts1.S) (s2: ts2.S) (ap: AP) :
            (labeling s1 s2 ap = .true) ↔ ((∃(ap1: ts1.AP), (ts1.labeling s1 ap1 = .true) ∧ (toAP1 ap1 = ap)) ∨ (∃(ap2: ts2.AP), (ts2.labeling s2 ap2 = .true) ∧ (toAP2 ap2 = ap)))

namespace Interleaving

variable {Act AP: Type _} {ts1 ts2: TransitionSystem}

inductive Transition (il: Interleaving Act AP ts1 ts2) : ts1.S → ts2.S → Act → ts1.S → ts2.S → Prop where
  | fst (s₁1: ts1.S) (a₁: ts1.Act) (s₁2: ts1.S) (req: s₁1 ─⌞a₁⌟→{ts1} s₁2) (s₂: ts2.S) : Transition il s₁1 s₂ (il.toAct1 a₁) s₁2 s₂
  | snd (s₂1: ts2.S) (a₂: ts2.Act) (s₂2: ts2.S) (req: s₂1 ─⌞a₂⌟→{ts2} s₂2) (s₁: ts1.S) : Transition il s₁ s₂1 (il.toAct2 a₂) s₁ s₂2

@[reducible]
def toTransitionSystem (il: Interleaving Act AP ts1 ts2) : TransitionSystem where
  S := ts1.S × ts2.S
  Act := ((Set.range il.toAct1) ∪ (Set.range il.toAct2): Set Act)
  I := Set.prod ts1.I ts2.I
  AP := ((Set.range il.toAP1) ∪ (Set.range il.toAP2): Set AP)
  L s ap := il.labeling s.fst s.snd ap.val
  tr s1 a s2 := Transition il s1.fst s1.snd a s2.fst s2.snd

/-
theorem toTransitionSystem_injective : Function.Injective (@toTransitionSystem Act AP ts1 ts2) := by
  rintro ⟨ac1_1, ap1_1, ac2_1, ap2_1, lb1, lm_lb1⟩
  rintro ⟨ac1_2, ap1_2, ac2_2, ap2_2, lb2, lm_lb2⟩
  simp [toTransitionSystem]
  intro lm1 lm2 lm3 lm4
  simp [Set.Elem] at lm1 lm2
-/
/-
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Function.Embedding.ext ?_
    intro act1
-/


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
