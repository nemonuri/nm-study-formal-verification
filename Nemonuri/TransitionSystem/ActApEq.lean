module

public import Nemonuri.TransitionSystem.Properties
public import Nemonuri.TransitionSystemLike.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem

universe u1 u2 u3

structure ActApEq (Act: Type u2) (AP: Type u3) extends toBasic: TransitionSystem.{u1, u2, u3} where
  valid: IsActApEq toBasic Act AP


namespace ActApEq

variable {Act: Type u2} {AP: Type u3}

theorem toBasic_injective : Function.Injective (ActApEq.toBasic: ActApEq Act AP → _) := by
  rintro ⟨tr1, lm1⟩ ⟨tr2, lm2⟩ lm3
  dsimp at lm3
  subst lm3
  rfl

instance transitionSystemLike : TransitionSystemLike (ActApEq Act AP) where
  coe := ActApEq.toBasic
  coe_injective := ActApEq.toBasic_injective



end ActApEq


end Nemonuri.TransitionSystem

end
