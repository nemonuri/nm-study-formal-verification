module

--public import Mathlib.Logic.Relation
public import Nemonuri.Relations.Heterogeneous.IsBiUnique

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*}

inductive SumRelGen (rel: αl → αr → Prop) : (αl ⊕ αr) → (αl ⊕ αr) → Prop where
  | intro (l: αl) (r: αr) (req: rel l r) : SumRelGen rel (.inl l) (.inr r)

variable {rel: αl → αr → Prop} {s1 s2: (αl ⊕ αr)}

namespace SumRelGen

theorem rel_exists (h: SumRelGen rel s1 s2) : ∃l r, rel l r ∧ s1 = .inl l ∧ s2 = .inr r := by
  rcases h with ⟨l, r, lm1⟩
  exists l; exists r

end SumRelGen

theorem sumRelGen_iff : (SumRelGen rel s1 s2) ↔ (∃l r, rel l r ∧ s1 = .inl l ∧ s2 = .inr r) := by
  constructor
  · exact SumRelGen.rel_exists
  · rintro ⟨l, r, lm1, lm2, lm3⟩
    subst lm2 lm3
    refine .intro _ _ lm1

def SumEquivGen (rel: αl → αr → Prop) : (αl ⊕ αr) → (αl ⊕ αr) → Prop := Relation.EqvGen (SumRelGen rel)

@[defeq]
theorem sumEquivGen_def {rel: αl → αr → Prop} : SumEquivGen rel = Relation.EqvGen (SumRelGen rel) := rfl



namespace SumEquivGen

def equivalence : Equivalence (SumEquivGen rel) := Relation.EqvGen.is_equivalence _

theorem eq_or_rel_exists (h: SumEquivGen rel s1 s2) (req: Relator.BiUnique rel) : (s1 = s2) ∨ (∃l r, rel l r ∧ ((s1 = .inl l ∧ s2 = .inr r) ∨ (s1 = .inr r ∧ s2 = .inl l))) := by
  dsimp [sumEquivGen_def] at h
  induction h with
  | rel _ _ lm1 =>
    rcases lm1.rel_exists with ⟨l, r, lm2, lm3, lm4⟩
    refine Or.inr ?_
    exists l; exists r
    refine ⟨lm2, ?_⟩
    refine Or.inl ?_
    exact ⟨lm3, lm4⟩
  | refl =>
    refine Or.inl ?_
    rfl
  | symm _ _ lm1 lm2 =>
    rcases lm2 with lm2 | lm2
    · exact Or.inl lm2.symm
    · rcases lm2 with ⟨l, r, lm2, lm3⟩
      refine Or.inr ?_
      exists l; exists r
      refine ⟨lm2, ?_⟩
      rcases lm3 with ⟨lm3, lm4⟩ | ⟨lm3, lm4⟩
      <;> (subst lm3 lm4; simp)
  | trans s1 s3 s2 _ _ lm1 lm2 =>
    rcases lm1 with lm1 | lm1
    <;> rcases lm2 with lm2 | lm2
    · exact Or.inl (lm1.trans lm2)
    · subst lm1
      rcases lm2 with ⟨l, r, lm2, lm3⟩
      rcases lm3 with ⟨lm3, lm4⟩ | ⟨lm3, lm4⟩
      <;> (subst lm3 lm4; simp; exact lm2)
    · subst lm2
      rcases lm1 with ⟨l, r, lm1, lm2⟩
      rcases lm2 with ⟨lm2, lm3⟩ | ⟨lm2, lm3⟩
      <;> (subst lm2 lm3; simp; exact lm1)
    · rcases lm1 with ⟨l, r, lm1, lm3⟩
      rcases lm3 with ⟨lm3, lm4⟩ | ⟨lm3, lm4⟩
      <;> (subst lm3 lm4; simp at lm2 ⊢)
      · rcases lm2 with ⟨l2, lm2, lm3⟩
        subst lm3
        simp
        exact req.left lm1 lm2
      · rcases lm2 with ⟨l2, lm2, lm3⟩
        subst lm3
        simp
        exact req.right lm1 lm2


    --dsimp only [← sumEquivGen_def] at lm1 lm2
    --have lm1 := SumEquivGen.eq_or_rel_exists_at s1 s3 lm1
    --have lm2 := SumEquivGen.eq_or_rel_exists_at s3 s2 lm2
    --have lm2 := @SumEquivGen.eq_or_rel_exists _ lm1



end SumEquivGen


theorem sumEquivGen_iff_of_biUnique (req: Relator.BiUnique rel) : SumEquivGen rel s1 s2 ↔ ((s1 = s2) ∨ (∃l r, rel l r ∧ ((s1 = .inl l ∧ s2 = .inr r) ∨ (s1 = .inr r ∧ s2 = .inl l)))) := by
  constructor
  · intro lm1
    exact SumEquivGen.eq_or_rel_exists lm1 req
  · intro lm1
    dsimp [sumEquivGen_def]
    rcases lm1 with lm1 | lm1
    · subst lm1
      exact .refl s1
    · rcases lm1 with ⟨l, r, lm1, lm2⟩
      rcases lm2 with ⟨lm2, lm3⟩ | ⟨lm2, lm3⟩
      <;> (subst lm2 lm3)
      · refine .rel _ _ ?_
        exact .intro _ _ lm1
      · refine .symm _ _ ?_
        refine .rel _ _ ?_
        exact .intro _ _ lm1

theorem sumEquivGen_iff [IsBiUnique rel] : SumEquivGen rel s1 s2 ↔ ((s1 = s2) ∨ (∃l r, rel l r ∧ ((s1 = .inl l ∧ s2 = .inr r) ∨ (s1 = .inr r ∧ s2 = .inl l)))) := sumEquivGen_iff_of_biUnique IsBiUnique.biUnique


/-
theorem sumEquivGen_iff_or {rel: αl → αr → Prop} {s1 s2: (αl ⊕ αr)}
  : (SumEquivGen rel) s1 s2 ↔ (s1 = s2 ∨ (∃(l: αl) (r: αr), rel l r ∧ ((s1 = .inl l ∧ s2 = .inr r) ∨ (s1 = .inr r ∧ s2 = .inl l)))) := by
  constructor
  · intro lm1
    dsimp [sumEquivGen_def] at lm1
    induction lm1 with
    | rel _ _ lm1 =>
      rcases lm1 with ⟨l, r, lm1⟩
      refine Or.inr ?_
      exists l
      exists r
      simp [lm1]
    | refl =>
      refine Or.inl ?_
      rfl
    | symm s1 s2 lm1 lm2 =>
      rcases lm2 with lm2 | lm2
      · exact Or.inl lm2.symm
      · rcases lm2 with ⟨l, r, lm2, lm3⟩
        refine Or.inr ?_
        exists l; exists r
        simp [lm2]
        rcases lm3 with ⟨lm3, lm4⟩ | ⟨lm3, lm4⟩
        <;> (subst lm3 lm4; simp)
    | trans s1 s2 s3 lm1 lm2 lm3 lm4 =>
      rcases lm3 with lm3 | lm3
      · subst lm3
        rcases lm4 with lm4 | lm4
        · exact Or.inl lm4
        · rcases lm4 with ⟨l, r, lm4, lm5⟩
          refine Or.inr ?_
          exists l; exists r
      · rcases lm3 with ⟨l1, r1, lm3_1, lm3_2⟩
        rcases lm4 with lm4 | lm4
        · subst lm4
          refine Or.inr ?_
          exists l1; exists r1
        · rcases lm4 with ⟨l2, r2, lm4_1, lm4_2⟩
          rcases lm3_2 with ⟨lm3_2, lm3_3⟩ | ⟨lm3_2, lm3_3⟩
          <;> (subst lm3_2 lm3_3; simp at lm4_2 ⊢)
          · rcases lm4_2 with ⟨lm4_2, lm4_3⟩
            subst lm4_2 lm4_3
            simp
-/
/-
          rcases lm4 with ⟨l2, r2, lm4_1, lm4_2⟩
          rcases lm3_2 with ⟨lm3_2, lm3_3⟩ | ⟨lm3_2, lm3_3⟩
          <;> subst lm3_2 lm3_3
          · simp at lm4_2
            rcases lm4_2 with ⟨lm4_2, lm4_3⟩
            subst lm4_2 lm4_3
            refine Or.inr ?_
            exists l2; exists r1
            simp [lm4_1]
-/


namespace SumEquivGen

@[reducible]
def setoidOf (rel: αl → αr → Prop) : Setoid (αl ⊕ αr) := Setoid.mk (SumEquivGen rel) (SumEquivGen.equivalence)

end SumEquivGen


def SumUnion (rel: αl → αr → Prop) : Type _ := Quotient (SumEquivGen.setoidOf rel)


def areEqSumOrRel [DecidableEq αl] [DecidableEq αr] (rel: αl → αr → Prop) [DecidableRel rel] : (αl ⊕ αr) → (αl ⊕ αr) → Bool
  | .inl l1, .inl l2 => decide (l1 = l2)
  | .inr r1, .inr r2 => decide (r1 = r2)
  | .inl l, .inr r | .inr r, .inl l => decide (rel l r)


namespace SumUnion

variable {rel: αl → αr → Prop}

def ofSum (s: αl ⊕ αr) : SumUnion rel := Quotient.mk _ s

def liftOfSum {β: Sort*} (f: (αl ⊕ αr) → β) (req: ∀(s1 s2: (αl ⊕ αr)), SumEquivGen rel s1 s2 → f s1 = f s2) (su: SumUnion rel) : β :=
  Quotient.lift f req su

@[defeq]
theorem liftOfSum_ofSum {β} {f: (αl ⊕ αr) → β} {req: ∀(s1 s2: (αl ⊕ αr)), SumEquivGen rel s1 s2 → f s1 = f s2} {s: (αl ⊕ αr)} : liftOfSum f req (.ofSum s) = f s := rfl


def liftOfSumOn₂ {βl βr: Type*} {rel2: βl → βr → Prop} {φ: Sort*} (su1: SumUnion rel) (su2: SumUnion rel2) (f: (αl ⊕ αr) → (βl ⊕ βr) → φ)
  (req: ∀as1 bs1 as2 bs2, SumEquivGen rel as1 as2 → SumEquivGen rel2 bs1 bs2 → f as1 bs1 = f as2 bs2)
  : φ :=
  Quotient.liftOn₂ su1 su2 f req

@[defeq]
theorem liftOfSumOn₂_ofSum {βl βr rel2 φ} {s1: (αl ⊕ αr)} {s2: (βl ⊕ βr)}
  {f: (αl ⊕ αr) → (βl ⊕ βr) → φ} {req: ∀as1 bs1 as2 bs2, SumEquivGen rel as1 as2 → SumEquivGen rel2 bs1 bs2 → f as1 bs1 = f as2 bs2}
  : liftOfSumOn₂ (.ofSum s1) (.ofSum s2) f req = f s1 s2 :=
  rfl

@[elab_as_elim]
theorem indOfSum
  {motive: SumUnion rel → Prop}
  (ofSum: (s: αl ⊕ αr) → motive (.ofSum s))
  (t: SumUnion rel)
  : motive t := by
  cases t using Quotient.ind
  rename_i s
  exact ofSum s


theorem ofSum_eq_iff_sumEquivGen {s1 s2: (αl ⊕ αr)} : ((ofSum s1: SumUnion rel) = ofSum s2) ↔ SumEquivGen rel s1 s2 := by
  dsimp [ofSum]
  constructor
  · intro lm1
    exact Quotient.exact lm1
  · intro lm1
    exact Quotient.sound lm1


def areEq [DecidableEq αl] [DecidableEq αr] [DecidableRel rel] [IsBiUnique rel] (su1 su2: SumUnion rel) : Bool :=
  su1.liftOfSumOn₂ su2 (areEqSumOrRel rel) (by
    intro as1 bs1 as2 bs2 lm1 lm2
    replace lm1 := lm1.eq_or_rel_exists IsBiUnique.biUnique
    replace lm2 := lm2.eq_or_rel_exists IsBiUnique.biUnique
    rcases as1 with ⟨al1⟩ | ⟨ar1⟩
    <;> rcases bs1 with ⟨bl1⟩ | ⟨br1⟩
    <;> rcases as2 with ⟨al2⟩ | ⟨ar2⟩
    <;> rcases bs2 with ⟨bl2⟩ | ⟨br2⟩
    <;> (
      simp at lm1 lm2 ⊢
      dsimp [areEqSumOrRel] )
    · subst lm1 lm2; rfl
    · subst lm1
      simp
      conv => lhs; rw [Eq.comm]
      exact IsBiUnique.left_eq_iff_rel lm2 al1
    · subst lm2
      simp
      exact IsBiUnique.left_eq_iff_rel lm1 bl1
    · simp
      exact IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm1 lm2
    · subst lm1
      simp
      symm
      conv => lhs; rw [Eq.comm]
      exact IsBiUnique.left_eq_iff_rel lm2 al1
    · subst lm1 lm2; rfl
    · simp
      exact IsBiUnique.rel_iff_rel_of_rel₂ lm1 lm2
    · subst lm2
      simp
      symm
      exact IsBiUnique.right_eq_iff_rel lm1 _
    · subst lm2
      simp
      symm
      exact IsBiUnique.left_eq_iff_rel lm1 _
    · simp
      exact IsBiUnique.rel_iff_rel_of_rel₂ lm2 lm1
    · subst lm1 lm2; rfl
    · subst lm1
      simp
      symm
      conv => lhs; rw [Eq.comm]
      exact IsBiUnique.right_eq_iff_rel lm2 _
    · simp
      symm
      exact IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm1 lm2
    · subst lm2
      simp
      exact IsBiUnique.right_eq_iff_rel lm1 _
    · subst lm1
      simp
      conv => lhs; rw [Eq.comm]
      exact IsBiUnique.right_eq_iff_rel lm2 _
    · subst lm1 lm2; rfl )

section AreEq

variable [DecidableEq αl] [DecidableEq αr] [DecidableRel rel] [IsBiUnique rel] {su1 su2: SumUnion rel}


theorem areEq_eq_true_iff_eq : (su1.areEq su2 = .true) ↔ (su1 = su2) := by
  cases su1 using indOfSum
  cases su2 using indOfSum
  rename_i s1 s2
  dsimp [areEq, liftOfSumOn₂_ofSum]
  symm
  refine Iff.trans ofSum_eq_iff_sumEquivGen ?_
  refine Iff.trans sumEquivGen_iff ?_
  rcases s1 with ⟨l1⟩ | ⟨r1⟩
  <;> rcases s2 with ⟨l2⟩ | ⟨r2⟩
  <;> simp [areEqSumOrRel]


instance : DecidableEq (SumUnion rel) := fun _ _ => decidable_of_decidable_of_iff areEq_eq_true_iff_eq


end AreEq

/-
    <;> (
      simp at lm1 lm2 ⊢
      conv => lhs; dsimp [areEqSumOrRel] )
    ·
-/




end SumUnion


end Nemonuri.Relations.Heterogeneous

end
