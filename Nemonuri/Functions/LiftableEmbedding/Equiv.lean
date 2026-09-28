module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

variable {L R L2 R2: Sort*}

def compEquivAndEmbed (lem: LiftableEmbedding L R) (el: L ≃ L2) (er: R ≃ R2) : L2 → R2 := er ∘ lem ∘ el.symm

theorem compEquivAndEmbed_exists_iff_isLiftable {lem: LiftableEmbedding L R} {el: L ≃ L2} {er: R ≃ R2} {rv2: R2}
  : (∃(lv2: L2), lem.compEquivAndEmbed el er lv2 = rv2) ↔ lem.IsLiftable (er.symm rv2) := by
  constructor
  · simp [compEquivAndEmbed]
    intro lv2 lm1
    rewrite [Eq.comm] at lm1
    subst lm1
    simp [IsLiftable.of_apply]
  · intro lm1
    dsimp [compEquivAndEmbed]
    cases lm1 using IsLiftable.induction
    rename_i lv lm1
    replace lm1 := congrArg er lm1
    simp at lm1
    subst lm1
    simp
    exists (el lv)
    simp

def compEquivAndLift (lem: LiftableEmbedding L R) (el: L ≃ L2) (er: R ≃ R2) (rv2: R2) (req: ∃(lv2: L2), lem.compEquivAndEmbed el er lv2 = rv2) : L2 :=
  el (lem.compEquivAndEmbed_exists_iff_isLiftable.mp req).lift


theorem compEquivAndEmbed_compEquivAndLift_eq_self {lem: LiftableEmbedding L R} {el: L ≃ L2} {er: R ≃ R2} {lv2: L2}
  : lem.compEquivAndLift el er (lem.compEquivAndEmbed el er lv2) (exists_apply_eq_apply _ _) = lv2 := by
  simp [compEquivAndEmbed, compEquivAndLift]
  rw [← el.symm.injective.eq_iff]
  simp
  exact IsLiftable.lift_eq_self _


def compEquiv (lem: LiftableEmbedding L R) (el: L ≃ L2) (er: R ≃ R2) : LiftableEmbedding L2 R2 where
  embed := lem.compEquivAndEmbed el er
  lift := lem.compEquivAndLift el er
  valid := by
    refine .mk ?_
    dsimp [RestrictedLeftInverse]
    intro lv
    exact lem.compEquivAndEmbed_compEquivAndLift_eq_self




end Nemonuri.Functions.LiftableEmbedding

end
