module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding


variable {L R: Type*}

def embedSet (lem: LiftableEmbedding L R) (s: Set L) : Set R := { rv: R | lem.embedPred (· ∈ s) rv }

theorem embedSet_mem_iff (lem: LiftableEmbedding L R) {s: Set L} {rv: R}
  : (rv ∈ lem.embedSet s) ↔ (∃(req: lem.IsLiftable rv), req.lift ∈ s) := by
  dsimp [embedSet, embedPred]
  simp only [dite_else_false]

theorem embedSet_injective {lem: LiftableEmbedding L R} : Function.Injective (lem.embedSet) := by
  intro s1 s2 lm1
  rewrite [Set.ext_iff] at ⊢ lm1
  intro lv
  specialize lm1 (lem lv)
  simp [embedSet_mem_iff, IsLiftable.of_apply] at lm1
  exact IsLiftable.pred_lift_iff_iff_self_iff.mp lm1


def liftSet (lem: LiftableEmbedding L R) (s: Set R) : Set L := { lv: L | lem.liftPred (· ∈ s) lv }

theorem liftSet_embedSet_leftInverse {lem: LiftableEmbedding L R} : Function.LeftInverse lem.liftSet lem.embedSet := by
  intro sl
  dsimp [liftSet, embedSet]
  rw [lem.liftPred_embedPred_leftInverse.eq]
  exact Set.setOf_mem_eq

theorem liftSet_surjective {lem: LiftableEmbedding L R} : Function.Surjective lem.liftSet := lem.liftSet_embedSet_leftInverse.surjective

--theorem liftSet_injective {lem: LiftableEmbedding L R}


theorem liftSet_mem_iff (lem: LiftableEmbedding L R) {s: Set R} {lv: L}
  : (lv ∈ lem.liftSet s) ↔ (lem lv ∈ s) := by
  dsimp [liftSet, liftPred]
  exact Iff.rfl


def ofSet (lem: LiftableEmbedding L R) : LiftableEmbedding (Set L) (Set R) where
  embed := lem.embedSet
  lift s _ := lem.liftSet s
  valid := by
    refine .mk ?_
    dsimp [RestrictedLeftInverse]
    exact lem.liftSet_embedSet_leftInverse

theorem set_elem_isLiftable_of_ofSet_isLiftable {lem: LiftableEmbedding L R} {rs: Set R} (req: lem.ofSet.IsLiftable rs) (rv: rs) : lem.IsLiftable rv.val := by
  revert rv
  simp only [Subtype.forall]
  intro rv lm1
  simp [isLiftable_iff_left_exists] at req
  rcases req with ⟨ls, lm2⟩
  dsimp [coe_def, ofSet] at lm2
  subst lm2
  simp [embedSet_mem_iff] at lm1
  rcases lm1 with ⟨lm1, _⟩
  exact lm1


theorem ofSet_isLiftable_iff {lem: LiftableEmbedding L R} {rs: Set R}
  : (lem.ofSet.IsLiftable rs) ↔ (∀(rv: rs), lem.IsLiftable rv.val) := by
  constructor
  · exact lem.set_elem_isLiftable_of_ofSet_isLiftable
  · simp only [Subtype.forall]
    intro lm1
    simp [isLiftable_iff_left_exists]
    exists (lem.liftSet rs)
    dsimp [coe_def, ofSet]
    simp [Set.ext_iff]
    intro rv
    simp [embedSet_mem_iff, liftSet_mem_iff]
    conv => rhs; arg 1; ext; arg 2; simp [IsLiftable.lift_apply_eq_self]
    simp
    exact lm1 rv





/-
instance (lem: LiftableEmbedding L R) : DecidablePred (lem.ofSet.IsLiftable ·) := fun _ => .isTrue (by
  simp [isLiftable_iff_left_exists])
-/

end Nemonuri.Functions.LiftableEmbedding

end
