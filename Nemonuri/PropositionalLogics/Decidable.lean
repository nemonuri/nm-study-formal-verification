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

--instance [DecidableEq AP] :

end SatRel


namespace Formula

variable {AP: Type*} [Fintype AP] [DecidableEq AP]

def areSyntaxEq : Formula AP → Formula AP → Bool
  | .true, .true => .true
  | .atom ap1, .atom ap2 => decide (ap1 = ap2)
  | .neg fml1, .neg fml2 => areSyntaxEq fml1 fml2
  | .and fmlL1 fmlR1, .and fmlL2 fmlR2 => (areSyntaxEq fmlL1 fmlL2) && (areSyntaxEq fmlR1 fmlR2)
  | _, _ => .false

theorem areSyntaxEq_eq_true_iff_eq {AP: Type*} [Fintype AP] [DecidableEq AP] {fml1 fml2: Formula AP}
  : (areSyntaxEq fml1 fml2 = .true) ↔ (fml1 = fml2) := by
  rcases fml1 with _ | ⟨ap1⟩ | ⟨fml1⟩ | ⟨fmlL1, fmlR1⟩
  <;> rcases fml2 with _ | ⟨ap2⟩ | ⟨fml2⟩ | ⟨fmlL2, fmlR2⟩
  <;> (dsimp [areSyntaxEq]; simp)
  · exact areSyntaxEq_eq_true_iff_eq
  · constructor
    · rintro ⟨lm1, lm2⟩
      refine ⟨?_, ?_⟩
      · exact areSyntaxEq_eq_true_iff_eq.mp lm1
      · exact areSyntaxEq_eq_true_iff_eq.mp lm2
    · rintro ⟨lm1, lm2⟩
      refine ⟨?_, ?_⟩
      · exact areSyntaxEq_eq_true_iff_eq.mpr lm1
      · exact areSyntaxEq_eq_true_iff_eq.mpr lm2

instance : DecidableEq (Formula AP) := fun _ _ => decidable_of_decidable_of_iff areSyntaxEq_eq_true_iff_eq

end Formula





end Nemonuri.PropositionalLogics

end
