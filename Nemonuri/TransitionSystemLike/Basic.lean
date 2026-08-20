module

public import Nemonuri.TransitionSystem


@[expose] public section

namespace Nemonuri

class TransitionSystemLike (α: Type _) where
  protected coe: α → TransitionSystem
  coe_injective: Function.Injective coe

attribute [coe] TransitionSystemLike.coe

instance {α: Type _} [TransitionSystemLike α] : CoeOut α TransitionSystem := ⟨TransitionSystemLike.coe⟩


end Nemonuri

end
