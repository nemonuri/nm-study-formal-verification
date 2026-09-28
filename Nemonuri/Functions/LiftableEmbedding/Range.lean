module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

variable {L R: Sort*}


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


end Nemonuri.Functions.LiftableEmbedding

end
