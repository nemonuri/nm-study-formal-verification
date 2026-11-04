module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*}


namespace SumUnion


def finsetOfLeftFinset (rel: αl → αr → Prop) [IsBiUnique rel] (fsL: Finset αl) : Finset (SumUnion rel) := fsL.map ⟨.ofSum ∘ .inl, inl_ofSum_injective⟩

def finsetOfRightFinset (rel: αl → αr → Prop) [IsBiUnique rel] (fsR: Finset αr) : Finset (SumUnion rel) := fsR.map ⟨.ofSum ∘ .inr, inr_ofSum_injective⟩


def hunionFinset (rel: αl → αr → Prop) [DecidableEq αl] [DecidableEq αr] [DecidableRel rel] [IsBiUnique rel] (fsL: Finset αl) (fsR: Finset αr) : Finset (SumUnion rel) :=
  (finsetOfLeftFinset rel fsL) ∪ (finsetOfRightFinset rel fsR)


protected instance fintype (rel: αl → αr → Prop) [DecidableEq αl] [DecidableEq αr] [DecidableRel rel] [IsBiUnique rel] [Fintype αl] [Fintype αr] : Fintype (SumUnion rel) where
  elems := hunionFinset rel (Finset.univ) (Finset.univ)
  complete := by
    intro su
    dsimp [hunionFinset, finsetOfLeftFinset, finsetOfRightFinset]
    simp
    cases su using indInlInrOfSum with
    | inl l =>
      left
      exists l
    | inr r =>
      right
      exists r


theorem finsetOfLeftFinset_coe_eq_coe_setOfLeftSet (rel: αl → αr → Prop) [IsBiUnique rel] (fsL: Finset αl) : ↑(finsetOfLeftFinset rel fsL) = setOfLeftSet rel ↑fsL := by
  refine Set.ext ?_
  intro su
  cases su using indInlInrOfSum <;> (
    dsimp [finsetOfLeftFinset]
    simp [sum_simp] )

theorem finsetOfRightFinset_coe_eq_coe_setOfRightSet (rel: αl → αr → Prop) [IsBiUnique rel] (fsR: Finset αr) : ↑(finsetOfRightFinset rel fsR) = setOfRightSet rel ↑fsR := by
  refine Set.ext ?_
  intro su
  cases su using indInlInrOfSum <;> (
    dsimp [finsetOfRightFinset]
    simp [sum_simp] )


theorem finsetOfLeftFinset_eq_finsetOfRightFinset_iff_setOfLeftSet_eq_setOfRightSet {rel: αl → αr → Prop} [IsBiUnique rel] {fsL: Finset αl} {fsR: Finset αr}
  : (finsetOfLeftFinset rel fsL = finsetOfRightFinset rel fsR) ↔ (setOfLeftSet rel ↑fsL = setOfRightSet rel ↑fsR) := by
  conv =>
    lhs
    rw [← SetLike.coe_injective.eq_iff, finsetOfLeftFinset_coe_eq_coe_setOfLeftSet rel fsL, finsetOfRightFinset_coe_eq_coe_setOfRightSet rel fsR]


end SumUnion

end Nemonuri.Relations.Heterogeneous

end
