module

public import Nemonuri.TransitionSystem


@[expose] public section

namespace Nemonuri

set_option pp.universes true

class TransitionSystemLike.{u1, u2, u3, u4} (α: Type u1) where
  protected coe: α → TransitionSystem.{u2, u3, u4}
  coe_injective: Function.Injective coe


attribute [coe, reducible] TransitionSystemLike.coe

instance {α: Type _} [TransitionSystemLike α] : CoeOut α TransitionSystem := ⟨TransitionSystemLike.coe⟩


end Nemonuri

end
