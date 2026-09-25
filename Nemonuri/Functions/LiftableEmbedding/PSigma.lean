module

public import Nemonuri.Functions.LiftableEmbedding.Pi

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

variable {L R: Sort*}

--#check PSigma.mk

def embedPSigma (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) : (lv : L) ×' mr (lem lv) → ((rv: R) ×' mr rv)
  | ⟨lv1, lv2⟩ => ⟨lem lv1, lv2⟩

theorem embedPSigma_injective {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} : Function.Injective (lem.embedPSigma mr) := by
  intro psl1 psl2 lm1
  simp [embedPSigma] at lm1
  refine PSigma.ext ?_ ?_
  · exact lm1.1
  · exact lm1.2



/-
def comapPSigma (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) : ((rv: R) ×' mr rv) → (lv : L) ×' mr (lem lv)
  | ⟨fstR, sndR⟩ =>
-/

end Nemonuri.Functions.LiftableEmbedding

end
