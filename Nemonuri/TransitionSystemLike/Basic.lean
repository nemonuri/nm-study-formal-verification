module

public import Nemonuri.TransitionSystem


@[expose] public section

namespace Nemonuri

class TransitionSystemLike.{u} (α: Type u) where
  protected coe: α → TransitionSystem.{u}
  coe_injective: Function.Injective coe


attribute [coe, reducible] TransitionSystemLike.coe

instance {α: Type _} [TransitionSystemLike α] : CoeOut α TransitionSystem := ⟨TransitionSystemLike.coe⟩


end Nemonuri

end
