module

public import Nemonuri.PropositionalLogics.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics

namespace SatRel

variable {E AP: Type*} [Fintype AP] [EvalLike E AP]

open Indicator

theorem defaultAt_isSat_iff {μ: E} {Φ: Formula AP}
  : (μ ⊨ₚ Φ) ↔ (evalFormulaToBool μ Φ = .true) := by
  dsimp [IsSat]
  conv =>
    lhs; dsimp [DFunLike.coe, defaultAt, Inhabited.default, SatRel.default]; rw [← AreEvalToTrue.eq_true_iff]
  rfl

instance {μ: E} {Φ: Formula AP} : Decidable (μ ⊨ₚ Φ) := decidable_of_iff' (evalFormulaToBool μ Φ = .true) defaultAt_isSat_iff


end SatRel



end Nemonuri.PropositionalLogics

end
