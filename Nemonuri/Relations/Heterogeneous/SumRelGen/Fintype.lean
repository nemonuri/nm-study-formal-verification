module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*}


namespace SumUnion


def finsetOfLeftFinset (rel: αl → αr → Prop) [IsBiUnique rel] (fsl: Finset αl) : Finset (SumUnion rel) := fsl.map ⟨.ofSum ∘ .inl, inl_ofSum_injective⟩

def finsetOfRightFinset (rel: αl → αr → Prop) [IsBiUnique rel] (fsr: Finset αr) : Finset (SumUnion rel) := fsr.map ⟨.ofSum ∘ .inr, inr_ofSum_injective⟩


def hunionFinset (rel: αl → αr → Prop) [DecidableEq αl] [DecidableEq αr] [DecidableRel rel] [IsBiUnique rel] (fsl: Finset αl) (fsr: Finset αr) : Finset (SumUnion rel) :=
  (finsetOfLeftFinset rel fsl) ∪ (finsetOfRightFinset rel fsr)


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

#check Finset.decidableEq

end SumUnion

end Nemonuri.Relations.Heterogeneous

end
