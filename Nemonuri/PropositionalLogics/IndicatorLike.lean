module

public import Nemonuri.PropositionalLogics.IsSat
public import Nemonuri.PropositionalLogics.FormulaLike

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics

class IndicatorLike (E: semiOutParam Type*) (AP: Type*) where
  protected coe : E → AP → Bool
  coe_injective : Function.Injective coe

attribute [coe] IndicatorLike.coe

namespace IndicatorLike

variable {E AP: Type*} --[Fintype AP]

instance [IndicatorLike E AP] : Coe E (Eval AP) where
  coe e := ⟨IndicatorLike.coe e⟩


variable (AP) in
protected def satRel : Eval.SatRel AP where
  rel μ fml := μ.evalFormula fml = .true
  valid μ := by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [pl_simp]

@[defeq, pl_simp]
theorem satRel_rel_def {μ fml} : (IndicatorLike.satRel AP).rel μ fml = (μ.evalFormula fml = .true) := rfl


instance [IndicatorLike E AP] : HasFormulaSatRel AP where
  satRel := IndicatorLike.satRel AP

@[defeq, pl_simp]
theorem coe_satRel_rel_def (e: E) (fml: Formula AP) [IndicatorLike E AP]
  : (HasFormulaSatRel.satRel.rel ↑e fml) = ((IndicatorLike.satRel AP).rel ↑e fml) :=
  rfl

open HasFormulaSatRel

instance (e: E) (fml: Formula AP) [IndicatorLike E AP] : Decidable (satRel.rel e fml) := decidable_of_decidable_of_eq satRel_rel_def.symm


example [IndicatorLike E AP] (e: E) (fml: Formula AP) : Decidable (e ⊨ₚ fml) := inferInstance


instance ofFinset [DecidableEq AP] : IndicatorLike (Finset AP) AP where
  coe fs ap := decide (ap ∈ fs)
  coe_injective := by
    intro fs1 fs2 lm1
    simp [funext_iff] at lm1
    simp [Finset.ext_iff]
    exact lm1


instance (F: Type*) [FormulaLike F AP] (e: E) (f: F) [IndicatorLike E AP] : Decidable (satRel.rel e (f: Formula AP)) := inferInstance


--example (e: E) (fml: Formula AP)

/-
def Mem (ap: AP) (e: E) : Prop := Eval.toIndicator e ap = .true

instance : Membership E AP where
  mem := Mem

variable {ap: AP} {e: E}

@[defeq, pl_simp]
theorem mem_def : (e ∈ ap) = (Eval.toIndicator e ap = .true) := rfl

instance : Decidable (e ∈ ap) := decidable_of_decidable_of_eq mem_def.symm
-/

/-
variable (E AP) in
@[reducible]
def toEvalLike : EvalLike E AP where
  coe := IndicatorLike.coe
  coe_injective := IndicatorLike.coe_injective
-/

/-
variable (E AP) in
def satRel : @SatRel E AP _ (toEvalLike E AP) :=
  letI : EvalLike E AP := toEvalLike E AP
  SatRel.default
-/

--instance (priority := low) (h: @SatRel E AP _ (toEvalLike E AP)) : EvalLike E AP := toEvalLike E AP

section Notation

/-
syntax:25 term:26 " ⊨ₚ " term:25 : term

macro_rules
  | `($μ ⊨ₚ $φ) => ``($μ ⊨ₚ{ _, _, _, toEvalLike _ _ } $φ)

syntax:23 term:24 " ≡ₚ " term:23 : term

macro_rules
  | `($p1 ≡ₚ $p2) => ``($p1 ≡ₚ{  } $p2)
-/

/-
syntax:23 term:24 " ≡ₚ⦃ " term " ⦄ " term:23 : term

macro_rules
  | `($p1 ≡ₚ⦃ $EC ⦄ $p2) => ``($p1 ≡ₚ{ defaultAt $EC _ } $p2)
-/

end Notation


end IndicatorLike

/-
instance (E AP: Type*) [Fintype AP] [IndicatorLike E AP] : SetLike AP E where
  coe ap := { μ: E | (IndicatorLike.coe μ).eval ap = .true }
  coe_injective := by
    intro ap1 ap2 lm1
    simp [Set.ext_iff] at lm1
    have lm2 := @IndicatorLike.coe_injective E AP _ _
    dsimp [Function.Injective] at lm2
-/


end Nemonuri.PropositionalLogics

end
