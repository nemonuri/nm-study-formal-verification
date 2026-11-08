module

public import Nemonuri.PropositionalLogics.IsSatRel

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics

class HasFormulaSatRel (AP: Type*) where
  satRel: Eval.SatRel AP


variable {AP: Type*} [HasFormulaSatRel AP]

def IsSat (fml: Formula AP) (μ: Eval AP) : Prop := HasFormulaSatRel.satRel.rel μ fml

@[defeq]
theorem isSat_def {fml: Formula AP} {μ: Eval AP} : IsSat fml μ = HasFormulaSatRel.satRel.rel μ fml := rfl


instance decidableIsSat (fml: Formula AP) (μ: Eval AP) [Decidable (HasFormulaSatRel.satRel.rel μ fml)] : Decidable (IsSat fml μ) :=
  decidable_of_decidable_of_eq isSat_def.symm

section Notation

syntax:25 term:26 " ⊨ₚ " term:25 : term
syntax:25 term:26 " ⊭ₚ " term:25 : term

macro_rules
  | `( $μ ⊨ₚ $φ ) => ``(IsSat $φ $μ)
  | `( $μ ⊭ₚ $φ ) => ``(¬($μ ⊨ₚ $φ))

end Notation

namespace HasFormulaSatRel

theorem valid_at (μ: Eval AP) : Eval.IsSatRel AP μ (HasFormulaSatRel.satRel.rel) := HasFormulaSatRel.satRel.valid μ

end HasFormulaSatRel

namespace IsSat

variable {μ: Eval AP}

@[scoped grind .]
theorem true_intro
  : μ ⊨ₚ (.true) := by
  dsimp [isSat_def]
  exact (HasFormulaSatRel.valid_at μ).true

@[scoped grind =]
theorem atom_iff (a: AP)
  : μ ⊨ₚ (.atom a) ↔ (μ a = .true) := by
  dsimp [isSat_def]
  exact (HasFormulaSatRel.valid_at μ).atom a

@[scoped grind =]
theorem neg_iff (p: Formula AP)
  : μ ⊨ₚ (¬ₚp) ↔ μ ⊭ₚ p := by
  dsimp [isSat_def]
  exact (HasFormulaSatRel.valid_at μ).neg p

@[scoped grind =]
theorem false_iff
  : μ ⊨ₚ (.false) ↔ False := by
  dsimp only [Formula.false]
  grind only [= neg_iff, true_intro]

@[scoped grind =]
theorem and_iff (p1 p2: Formula AP)
  : μ ⊨ₚ (p1 ∧ₚ p2) ↔ (μ ⊨ₚ p1) ∧ (μ ⊨ₚ p2) := by
  dsimp [isSat_def]
  exact (HasFormulaSatRel.valid_at μ).and p1 p2

@[scoped grind =]
theorem or_iff (p1 p2: Formula AP)
  : μ ⊨ₚ (p1 ∨ₚ p2) ↔ (μ ⊨ₚ p1) ∨ (μ ⊨ₚ p2) := by
  dsimp only [Formula.or]
  grind

theorem imp_iff_or (p1 p2: Formula AP)
  : μ ⊨ₚ (p1 →ₚ p2) ↔ (μ ⊭ₚ p1) ∨ (μ ⊨ₚ p2) := by
  dsimp only [Formula.imp]
  grind

@[scoped grind =]
theorem imp_iff_imp (p1 p2: Formula AP)
  : μ ⊨ₚ (p1 →ₚ p2) ↔ ((μ ⊨ₚ p1) → (μ ⊨ₚ p2)) := by
  simp only [imp_iff_or]
  grind only

attribute [pl_simp] true_intro atom_iff neg_iff false_iff and_iff or_iff imp_iff_imp

end IsSat

variable (AP) in
def IsSatisfiable (p: Formula AP) : Prop := ∃μ, μ ⊨ₚ p

variable (AP) in
def IsValid (p: Formula AP) : Prop := ∀μ, μ ⊨ₚ p

variable (AP) in
abbrev IsUnsatisfiable (p: Formula AP) : Prop := ¬(IsSatisfiable AP p)

theorem unsatisfiable_iff_neg_valid (p: Formula AP)
  : IsUnsatisfiable AP p ↔ IsValid AP (¬ₚp) := by
  simp only [IsUnsatisfiable, IsSatisfiable, IsValid]
  simp only [not_exists]
  simp only [IsSat.neg_iff]

end Nemonuri.PropositionalLogics

end
