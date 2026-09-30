module

public import Nemonuri.Functions.LiftableEmbedding.Equiv

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

universe uu us


structure SubBundled (Univ: Sort uu) where
  Sub: Sort us
  liftableEmbedding: LiftableEmbedding Sub Univ

namespace SubBundled

variable {Univ: Sort uu}

@[ext]
protected theorem ext {sb1 sb2: SubBundled Univ} (req1: sb1.Sub = sb2.Sub) (req2: sb1.liftableEmbedding.embed ≍ sb2.liftableEmbedding.embed) : sb1 = sb2 := by
  rcases sb1 with ⟨s1, lm1⟩
  rcases sb2 with ⟨s2, lm2⟩
  dsimp at req1
  subst req1
  simp at req2 ⊢
  exact LiftableEmbedding.embed_ext req2

@[ext]
protected theorem ext_lift {sb1 sb2: SubBundled Univ}
  (req1: sb1.Sub = sb2.Sub)
  (req2: ∀(uv: Univ), sb1.liftableEmbedding.IsLiftable uv ↔ sb2.liftableEmbedding.IsLiftable uv)
  (req3: ∀(uv: Univ) (req3_1: sb1.liftableEmbedding.IsLiftable uv) (req3_2: sb2.liftableEmbedding.IsLiftable uv), req3_1.lift ≍ req3_2.lift)
  : sb1 = sb2 := by
  rcases sb1 with ⟨Sub1, lem1⟩
  rcases sb2 with ⟨Sub2, lem2⟩
  dsimp at req1
  subst req1
  simp at req2 req3 ⊢
  simp [DFunLike.ext_iff]
  intro s1
  let uv : Univ := lem1 s1
  specialize req2 uv
  specialize req3 uv
  have lm1 : lem1.IsLiftable uv := by subst uv; exact IsLiftable.of_apply
  simp [lm1] at req2
  specialize req3 lm1 req2
  subst uv
  rewrite [lm1.lift_eq_self] at req3
  cases req2 using IsLiftable.induction
  rename_i s2 lm2
  conv at req3 => rhs; simp only [lm2]; rewrite [IsLiftable.lift_eq_self]
  subst req3
  exact lm2


--  (req: ∀(sv1: sb1.Sub) (sv2: sb2.Sub) (req_1: sb1.liftableEmbedding.IsLiftable (sb2.liftableEmbedding sv2) ))

def toPLifted (sb: SubBundled Univ) : SubBundled (PLift Univ) where
  Sub := sb.Sub
  liftableEmbedding := sb.liftableEmbedding.compEquiv (Equiv.refl _) (Equiv.plift.symm)

def ofPLifted (sb: SubBundled.{uu+1, us} (PLift.{uu} Univ)) : SubBundled.{uu, us} Univ where
  Sub := sb.Sub
  liftableEmbedding := sb.liftableEmbedding.compEquiv (Equiv.refl _) (Equiv.plift)


theorem ofPLifted_toPLifted_leftInverse : Function.LeftInverse ofPLifted (@toPLifted Univ) := by
  rintro ⟨Sub, lem⟩
  dsimp [toPLifted, ofPLifted]
  rfl

theorem ofPLifted_toPLifted_rightInverse : Function.RightInverse ofPLifted (@toPLifted Univ) := by
  rintro ⟨Sub, lem⟩
  dsimp [toPLifted, ofPLifted]
  rfl


def equivToPLifted : SubBundled Univ ≃ SubBundled (PLift Univ) where
  toFun := toPLifted
  invFun := ofPLifted


--def isLiftable (sb: SubBundled Univ) (uv: Univ) [Decidable (sb.liftableEmbedding.IsLiftable uv)] : Bool := decide (sb.liftableEmbedding.IsLiftable uv)

--def classicalIsLiftable

end SubBundled



end Nemonuri.Functions.LiftableEmbedding

end
