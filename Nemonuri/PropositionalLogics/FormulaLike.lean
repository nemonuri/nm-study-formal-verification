module

public import Nemonuri.PropositionalLogics.Formula


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics


class FormulaLike (F: Type*) (AP: semiOutParam Type*) where
  coe: F → Formula AP
  coe_injective: Function.Injective coe

attribute [coe] FormulaLike.coe

instance (F AP) [FormulaLike F AP] : CoeOut F (Formula AP) := ⟨FormulaLike.coe⟩

end Nemonuri.PropositionalLogics

end
