module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding


def Range {L R: Sort*} (lem: LiftableEmbedding L R) : Sort _ := Subtype (lem.IsLiftable)

@[defeq]
theorem range_def {L R: Sort*} {lem: LiftableEmbedding L R} : lem.Range = Subtype (lem.IsLiftable) := rfl


section

variable {L R: Sort*} {lem: LiftableEmbedding L R}

namespace Range

def equivToSubtype : lem.Range ≃ Subtype (lem.IsLiftable) := Equiv.cast lem.range_def

theorem nonempty_iff_exists : Nonempty (lem.Range) ↔ ∃(rv: R), lem.IsLiftable rv := by simp [range_def]

end Range

def rangeOfLeft (lem: LiftableEmbedding L R) (lv: L) : lem.Range := ⟨lem lv, .of_apply⟩

def rangeToLeft (lem: LiftableEmbedding L R) (ran: lem.Range) : L := ran.property.lift

theorem rangeToLeft_rangeOfLeft_leftInverse : Function.LeftInverse lem.rangeToLeft lem.rangeOfLeft := by
  intro lv
  dsimp [rangeOfLeft, rangeToLeft]
  exact IsLiftable.lift_eq_self _

theorem rangeToLeft_rangeOfLeft_rightInverse : Function.RightInverse lem.rangeToLeft lem.rangeOfLeft := by
  rintro ⟨rv, lm1⟩
  dsimp [rangeOfLeft, rangeToLeft]
  congr
  rw [IsLiftable.lift_apply_eq_self]


def equivOfRangeToLeft (lem: LiftableEmbedding L R) : lem.Range ≃ L where
  toFun := lem.rangeToLeft
  invFun := lem.rangeOfLeft
  left_inv := lem.rangeToLeft_rangeOfLeft_rightInverse
  right_inv := lem.rangeToLeft_rangeOfLeft_leftInverse


namespace Range

theorem nonempty_iff_nonempry : Nonempty (lem.Range) ↔ Nonempty L := by
  constructor
  · rintro ⟨ran⟩
    exact .intro (lem.equivOfRangeToLeft ran)
  · rintro ⟨lv⟩
    exact .intro (lem.equivOfRangeToLeft.symm lv)

theorem isEmpty_iff_forall : IsEmpty (lem.Range) ↔ ∀(rv: R), ¬lem.IsLiftable rv := by
  rw [← not_iff_not]
  simp
  exact nonempty_iff_exists

theorem isEmpty_iff_isEmpty : IsEmpty (lem.Range) ↔ IsEmpty L := by
  rw [← not_iff_not]
  simp
  exact nonempty_iff_nonempry


end Range

end

variable {L1 R L2: Sort*}

def RangeEq (lem1: LiftableEmbedding L1 R) (lem2: LiftableEmbedding L2 R) : Prop := lem1.IsLiftable = lem2.IsLiftable

variable {lem1: LiftableEmbedding L1 R} {lem2: LiftableEmbedding L2 R}

@[defeq]
theorem rangeEq_def : lem1.RangeEq lem2 = (lem1.IsLiftable = lem2.IsLiftable) := rfl

theorem rangeEq_iff_forall : (lem1.RangeEq lem2) ↔ (∀(rv: R), lem1.IsLiftable rv ↔ lem2.IsLiftable rv) := by
  dsimp [rangeEq_def]
  simp [funext_iff]


namespace RangeEq

theorem isLiftable_iff (h: lem1.RangeEq lem2) {rv: R} : (lem1.IsLiftable rv) ↔ (lem2.IsLiftable rv) := lem1.rangeEq_iff_forall.mp h rv

def rangeEquiv (h: lem1.RangeEq lem2) : lem1.Range ≃ lem2.Range where
  toFun ran1 := ⟨ran1.val, h.isLiftable_iff.mp ran1.property⟩
  invFun ran2 := ⟨ran2.val, h.isLiftable_iff.mpr ran2.property⟩

def leftEquiv (h: lem1.RangeEq lem2) : L1 ≃ L2 where
  toFun := lem2.equivOfRangeToLeft ∘ h.rangeEquiv ∘ lem1.equivOfRangeToLeft.symm
  invFun := lem1.equivOfRangeToLeft ∘ h.rangeEquiv.symm ∘ lem2.equivOfRangeToLeft.symm
  left_inv := by intro _; simp
  right_inv := by intro _; simp

theorem to_hetero_liftable (h: lem1.RangeEq lem2) : (∀(lv1: L1), lem2.IsLiftable (lem1 lv1)) ∧ (∀(lv2: L2), lem1.IsLiftable (lem2 lv2)) := by
  refine ⟨?_, ?_⟩
  · intro lv1
    rw [← h.isLiftable_iff]
    exact IsLiftable.of_apply
  · intro lv2
    rw [h.isLiftable_iff]
    exact IsLiftable.of_apply

theorem of_hetero_liftable (req1: ∀(lv1: L1), lem2.IsLiftable (lem1 lv1)) (req2: ∀(lv2: L2), lem1.IsLiftable (lem2 lv2)) : lem1.RangeEq lem2 := by
  rw [rangeEq_iff_forall]
  intro rv
  by_cases lm1: lem1.IsLiftable rv
  · simp [lm1]
    cases lm1 using IsLiftable.induction
    rename_i lv lm1
    subst lm1
    exact req1 lv
  · by_cases lm2: lem2.IsLiftable rv
    · cases lm2 using IsLiftable.induction
      rename_i lv lm2
      subst lm2
      specialize req2 lv
      contradiction
    · simp [lm1, lm2]

/-
    simp [isLiftable_iff_left_exists]
    exists (h.leftEquiv lv1)
    dsimp [leftEquiv, equivOfRangeToLeft, rangeEquiv, rangeOfLeft, rangeToLeft]
-/
/-
  rcases isEmpty_or_nonempty R with lm1 | lm1
  · have lm2_1 : IsEmpty L1 := lem1.isEmpty_left_of_isEmpty_right
    have lm2_2 : IsEmpty L2 := lem2.isEmpty_left_of_isEmpty_right
    simp
  · refine ⟨?_, ?_⟩
    ·
-/
/-
theorem of_subtype_equiv (e: Subtype (lem1.IsLiftable) ≃ Subtype (lem2.IsLiftable)) : lem1.RangeEq lem2 := by
  have lm1 := e.left_inv'
-/

end RangeEq


--def Range (lem: LiftableEmbedding L R) ⦃rv: R⦄ : Prop :=

/-
structure Range (lem: LiftableEmbedding L R) : Sort _ where
  Mem (rv: R) : Prop
  valid (rv: R) : Mem rv ↔ lem.IsLiftable rv

def toRange (lem: LiftableEmbedding L R) : lem.Range where
  Mem (rv: R) := lem.IsLiftable rv
  valid _ := Iff.rfl

/-
def Range (R: Sort*) : Type _ := Set (PLift R)

@[defeq]
theorem range_def {R: Sort*} : Range R = Set (PLift R) := rfl
-/
namespace Range

variable {lem: LiftableEmbedding L R}

protected instance subsingleton : Subsingleton (lem.Range) where
  allEq := by
    rintro ⟨m1, lm1⟩ ⟨m2, lm2⟩
    simp [funext_iff]
    intro rv
    specialize lm1 rv
    specialize lm2 rv
    exact lm1.trans lm2.symm

protected instance unique : Unique (lem.Range) where
  default := lem.toRange
  uniq _ := Subsingleton.elim _ _

theorem mem_eq_isLiftable {ran: lem.Range} : ran.Mem = lem.IsLiftable := by

end Range
-/


--variable {L R: Sort*}

--def Range (lem: LiftableEmbedding L R) : Type _ := Set (PLift R)

/-
def Liftable (lem: LiftableEmbedding L R) : Sort _ := { rv: R // lem.IsLiftable rv }

@[defeq]
theorem liftable_def {lem: LiftableEmbedding L R} : lem.Liftable = { rv: R // lem.IsLiftable rv } := rfl
-/


/-
structure Range (lem: LiftableEmbedding L R) : Sort _ where
  toDecidable (rv: R) : Decidable (lem.IsLiftable rv)

namespace Range

variable {lem: LiftableEmbedding L R}


noncomputable def ofClassical : lem.Range := ⟨fun rv => Classical.propDecidable (lem.IsLiftable rv)⟩


protected instance subsingleton : Subsingleton (lem.Range) where
  allEq := by
    rintro ⟨r1⟩ ⟨r2⟩
    simp
    exact Subsingleton.elim _ _

@[reducible]
def toUnique (ran: lem.Range) : Unique lem.Range where
  default := ran
  uniq _ := Range.subsingleton.elim _ _

noncomputable instance (priority := low) classicalUnique : Unique lem.Range := ofClassical.toUnique

end Range


noncomputable def classicalRange (lem: LiftableEmbedding L R) : lem.Range := Range.ofClassical


namespace Range

variable {lem: LiftableEmbedding L R}

def contains (ran: lem.Range) (rv: R) : Bool := (ran.toDecidable rv).decide _



variable {ran: lem.Range} {L2: Sort*} {lem2: LiftableEmbedding L2 R} {ran2: lem2.Range}

theorem contains_eq_true_iff {rv: R} : (ran.contains rv = .true) ↔ lem.IsLiftable rv := by simp [contains]

theorem contains_eq_iff_iff {rv: R} : (ran.contains rv = ran2.contains rv) ↔ (lem.IsLiftable rv ↔ lem2.IsLiftable rv) := by
  rw [Bool.eq_iff_iff]
  simp [contains_eq_true_iff]

theorem contains_eq_false_iff {rv: R} : (ran.contains rv = .false) ↔ ¬lem.IsLiftable rv := by simp [contains]

theorem contains_eq_iff_forall_iff : (ran.contains = ran2.contains) ↔ (∀(rv: R), lem.IsLiftable rv ↔ lem2.IsLiftable rv) := by
  rw [funext_iff]
  refine forall_congr' ?_
  intro _
  exact contains_eq_iff_iff

end Range

def RangeEq {L1 R L2: Sort*} (lem1: LiftableEmbedding L1 R) (lem2: LiftableEmbedding L2 R) : Prop := ∀⦃rv: R⦄, lem1.IsLiftable rv ↔ lem2.IsLiftable rv

section

variable {L1 R L2: Sort*} {lem1: LiftableEmbedding L1 R} {lem2: LiftableEmbedding L2 R}

@[defeq]
theorem rangeEq_def : lem1.RangeEq lem2 = (∀(rv: R), lem1.IsLiftable rv ↔ lem2.IsLiftable rv) := rfl

variable {ran1: lem1.Range} {ran2: lem2.Range}

theorem Range.contains_eq_iff_rangeEq : (ran1.contains = ran2.contains) ↔ lem1.RangeEq lem2 := by
  rw [Range.contains_eq_iff_forall_iff]
  rw [← propext_iff]
  dsimp [rangeEq_def]

namespace RangeEq

theorem of_range_contains_eq (ran1: lem1.Range) (ran2: lem2.Range) (req: ran1.contains = ran2.contains) : lem1.RangeEq lem2 := by
  revert req
  exact Range.contains_eq_iff_rangeEq.mp

/-
theorem of_range_equiv (re: lem1.Range ≃ lem2.Range) : lem1.RangeEq lem2 := by
  let ran1: lem1.Range := .ofClassical
-/
/-
  refine of_range_contains_eq ran1 (re ran1) ?_
  refine funext ?_
  intro rv
-/



end RangeEq

end

--def Range (lem: LiftableEmbedding L R) : Type _ := Set (PLift R)


--theorem range_def {lem: LiftableEmbedding L R} : lem.Range = (∀(rv: R), lem.IsLiftable rv) := rfl
-/

end Nemonuri.Functions.LiftableEmbedding

end
