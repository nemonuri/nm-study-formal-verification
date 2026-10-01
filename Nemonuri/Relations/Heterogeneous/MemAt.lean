module

public import Nemonuri.Relations.Heterogeneous.Label
public import Mathlib.Logic.Relator

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

variable {α β: Sort uh}

inductive MemAt (rel: α → β → Prop) : (lb: Label) → (lb.MatchSort α β) → Prop where
  | fst (a: α) (b: β) (req: rel a b) : MemAt rel .fst a
  | snd (a: α) (b: β) (req: rel a b) : MemAt rel .snd b

namespace MemAt

structure Decider (rel: α → β → Prop) where
  decRel (a: α) (b: β) : Decidable (rel a b)
  decMemAt (lb: Label) (x: lb.MatchSort α β) : Decidable (MemAt rel lb x)

variable {rel: α → β → Prop}

/-
theorem rel_of_fst_snd_of_biUnique {a: α} {b: β} (req1: MemAt rel .fst a) (req2: MemAt rel .snd b) (req3: Relator.BiUnique rel) : rel a b := by --(req1: Relator.BiUnique rel)
  cases req1
  rename_i b2 lm1
  cases req2
  rename_i a2 lm2
  rcases req3 with ⟨lm3, lm4⟩
  dsimp [Relator.LeftUnique] at lm3
  dsimp [Relator.RightUnique] at lm4
  by_cases lm5: a = a2
  · subst lm5; exact lm2
  · by_cases lm6: b = b2
    · subst lm6; exact lm1
    · specialize @lm3 a a2 b2
      simp [lm5] at lm3
      specialize @lm4 a2 b b2
      simp [lm6] at lm4
-/

/-
  have lm3_1 := @lm3 a a2 b
  have lm3_2 := @lm3 a a2 b2
  have lm4_1 := @lm4 a b b2
  have lm4_2 := @lm4 a2 b b2
  simp [lm1] at lm3_2 lm4_1
  simp [lm2] at lm3_1 lm4_2
  false_or_by_contra
  rename_i lm5
-/

  --have lm4_1 := @lm4
  --specialize @lm3_2
  --rcases req1 with ⟨_, b2, lm1⟩
  --rcases req2 with ⟨a2, _, lm2⟩

/-
theorem fst_and_snd_iff_rel (req: Relator.LeftUnique rel) {a: α} {b: β} : ((MemAt rel .fst a) ∧ (MemAt rel .snd b)) ↔ rel a b := by
  constructor
  · rintro ⟨lm1, lm2⟩
    cases lm1
    cases lm2
-/



end MemAt


inductive NotMemAt (rel: α → β → Prop) : (lb: Label) → (lb.MatchSort α β) → Prop where
  | fst (a: α) (req: ∀(b: β), ¬(rel a b)) : NotMemAt rel .fst a
  | snd (b: β) (req: ∀(a: α), ¬(rel a b)) : NotMemAt rel .snd b

theorem memAt_or_notMemAt (rel: α → β → Prop) (lb: Label) (x: lb.MatchSort α β) : MemAt rel lb x ∨ NotMemAt rel lb x := by
  rcases lb <;> dsimp at x
  · by_cases lm1: ∃b, rel x b
    · rcases lm1 with ⟨b, lm1⟩
      refine Or.inl ?_
      exact MemAt.fst x b lm1
    · simp at lm1
      refine Or.inr ?_
      exact NotMemAt.fst x lm1
  · by_cases lm1: ∃a, rel a x
    · rcases lm1 with ⟨a, lm1⟩
      refine Or.inl ?_
      exact MemAt.snd a x lm1
    · simp at lm1
      refine Or.inr ?_
      exact NotMemAt.snd x lm1

theorem not_memAt_iff_notMemAt (rel: α → β → Prop) (lb: Label) (x: lb.MatchSort α β) : ¬(MemAt rel lb x) ↔ NotMemAt rel lb x := by
  constructor
  · intro lm1
    have lm2 := memAt_or_notMemAt rel lb x
    simpa [lm1] using lm2
  · rcases lb <;> (
      dsimp at x
      intro lm1 lm2
      rcases lm1 with ⟨x, lm1⟩ | ⟨x, lm1⟩
      rcases lm2 with ⟨a, b, lm2⟩ | ⟨a, b, lm2⟩)
    · exact lm1 b lm2
    · exact lm1 a lm2

theorem not_notMemAt_iff_memAt (rel: α → β → Prop) (lb: Label) (x: lb.MatchSort α β) : ¬(NotMemAt rel lb x) ↔ (MemAt rel lb x) := by
  let dc1 : Decidable (MemAt rel lb x) := Classical.propDecidable _
  let dc2 : Decidable (NotMemAt rel lb x) := Classical.propDecidable _
  rewrite [Decidable.not_iff_comm]
  exact not_memAt_iff_notMemAt rel lb x


def ElemAt (rel: α → β → Prop) (lb: Label) : Sort _ := Subtype (MemAt rel lb)

def ComplElemAt (rel: α → β → Prop) (lb: Label) : Sort _ := Subtype (NotMemAt rel lb)

theorem elemAt_complElemAt_val_ne {rel: α → β → Prop} {lb: Label} {e: ElemAt rel lb} {ce: ComplElemAt rel lb} : e.val ≠ ce.val := by
  rcases e with ⟨e, lm1⟩
  rcases ce with ⟨ce, lm2⟩
  dsimp
  intro lm3
  subst lm3
  exact (not_memAt_iff_notMemAt rel lb e).mpr lm2 lm1


end Nemonuri.Relations.Heterogeneous

end
