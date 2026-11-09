module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} {rel: αl → αr → Prop}

namespace SumUnion


structure CanShare (su: SumUnion rel) : Prop where
  left : ∃(l: αl), su = (.ofSum (.inl l))
  right : ∃(r: αr), su = (.ofSum (.inr r))

def hasLeftRight [IsBiUnique rel] [HasPartialCongruence rel] (su: SumUnion rel) : Bool := su.left?.isSome && su.right?.isSome

namespace CanShare

variable {su: SumUnion rel} [IsBiUnique rel] [HasPartialCongruence rel]

theorem of_hasLeftRight_eq_true (req: su.hasLeftRight = .true) : su.CanShare := by
  simp [hasLeftRight, Option.isSome_iff_exists] at req
  rcases req with ⟨lm1, lm2⟩
  simp [sum_simp] at lm1 lm2
  exact ⟨lm1, lm2⟩

theorem hasLeftRight_eq_true (h: su.CanShare) : su.hasLeftRight = .true := by
  rcases h with ⟨lm1, lm2⟩
  rcases lm1 with ⟨l, lm1⟩
  rcases lm2 with ⟨r, lm2⟩
  subst lm2
  simp [sum_simp] at lm1
  simp [hasLeftRight, sum_simp, Option.isSome_iff_exists]
  exists l

instance : Decidable (su.CanShare) := decidable_of_iff (su.hasLeftRight = .true) (Iff.intro of_hasLeftRight_eq_true hasLeftRight_eq_true)

end CanShare



end SumUnion

end Nemonuri.Relations.Heterogeneous
