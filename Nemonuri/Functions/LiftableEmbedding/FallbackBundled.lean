module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

universe ul ur umr

structure FallbackBundledStruct (L: Type ul) (R: Type ur) (mr: R → Type umr)
  extends toBasic: LiftableEmbeddingStructure L R where
  fallback (rv: R) (req: rv ∉ Set.range toBasic.embed) : mr rv

structure FallbackBundled (L: Type ul) (R: Type ur) (mr: R → Type umr)
  extends toStruct: FallbackBundledStruct L R mr where
  valid: IsLiftableEmbedding toStruct.toBasic


namespace FallbackBundled

variable {L: Type ul} {R: Type ur} {mr: R → Type umr}

def toDomainLiftableEmbedding (fbb: FallbackBundled L R mr) : LiftableEmbedding L R := .mk fbb.toStruct.toBasic fbb.valid

def toFallback (fbb: FallbackBundled L R mr) : fbb.toDomainLiftableEmbedding.Fallback mr := .mk (fbb.fallback)


@[ext]
protected theorem ext
  (fbb1 fbb2: FallbackBundled L R mr)
  (req1: fbb1.toDomainLiftableEmbedding = fbb2.toDomainLiftableEmbedding)
  (req2: (∀(rv: R) (req2_1: ¬fbb1.toDomainLiftableEmbedding.IsLiftable rv) (req2_2: ¬fbb2.toDomainLiftableEmbedding.IsLiftable rv), fbb1.toFallback rv req2_1 = fbb2.toFallback rv req2_2) )
  : fbb1 = fbb2 := by
  simp only [req1, Subsingleton.forall₂_iff] at req2
  revert req1
  simp [DFunLike.ext_iff]
  intro lm1 lm2
  dsimp only [toDomainLiftableEmbedding, toFallback, DFunLike.coe] at lm1 lm2
  simp [isLiftable_iff_left_exists] at lm2
  dsimp only [DFunLike.coe] at lm2
  rcases fbb1 with ⟨fbb1, ⟨lm_fbb1⟩⟩
  rcases fbb2 with ⟨fbb2, ⟨lm_fbb2⟩⟩
  rcases fbb1 with ⟨⟨e1, l1⟩, fb1⟩
  rcases fbb2 with ⟨⟨e2, l2⟩, fb2⟩
  dsimp at lm1 lm2 fb1 fb2 lm_fbb1 lm_fbb2
  have lm3: e1 = e2 := funext lm1
  subst lm3
  have lm3_1 := lm_fbb1.eq
  have lm3_2 := lm_fbb2.eq
  congr
  · simp [funext_iff]
    intro rv lv lm4
    have lm4_1 := lm4.symm
    subst lm4_1
    specialize lm3_1 lv
    specialize lm3_2 lv
    simp [lm3_1, lm3_2]
  · simp [funext_iff]
    conv at lm2 => ext; arg -2; ext; arg -1; rw [Eq.comm]
    exact lm2



def toPiLiftableEmbedding (fbb: FallbackBundled L R mr) [DecidablePred (fbb.toDomainLiftableEmbedding.IsLiftable ·)] : LiftableEmbedding ((lv: L) → mr (fbb.toDomainLiftableEmbedding lv)) ((rv: R) → mr rv) :=
  fbb.toFallback.toLiftableEmbedding

end FallbackBundled

end Nemonuri.Functions.LiftableEmbedding

end
