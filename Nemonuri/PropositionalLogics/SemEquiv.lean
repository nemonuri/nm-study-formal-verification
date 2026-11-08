module

public import Nemonuri.PropositionalLogics.IsSat

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics

variable {AP: Type*} [HasFormulaSatRel AP]

variable (AP) in
/-- `p1` `p2` are semantically equivalent -/
def SemEquiv (p1 p2: Formula AP) : Prop := ∀⦃μ: Eval AP⦄, (μ ⊨ₚ p1) ↔ (μ ⊨ₚ p2)


section Notation

syntax:23 term:24 " ≡ₚ " term:23 : term

macro_rules
  | `($p1 ≡ₚ $p2) => ``(SemEquiv _ $p1 $p2)

end Notation



@[defeq, scoped grind =]
theorem semEquiv_def (p1 p2: Formula AP) : SemEquiv AP p1 p2 = (∀(μ: Eval AP), (μ ⊨ₚ p1) ↔ (μ ⊨ₚ p2)) := rfl

namespace SemEquiv

--variable {sr} in
theorem forall_iff {p1 p2: Formula AP} (h: p1 ≡ₚ p2) (μ: Eval AP) : (μ ⊨ₚ p1) ↔ (μ ⊨ₚ p2) := by
  dsimp [semEquiv_def] at h
  exact h μ

--variable {sr} in
theorem subst_mp {p1 p2: Formula AP} (h: p1 ≡ₚ p2) {μ: Eval AP} : (μ ⊨ₚ p1) → (μ ⊨ₚ p2) := (h.forall_iff μ).mp

--variable {sr} in
theorem subst_mpr {p1 p2: Formula AP} (h: p1 ≡ₚ p2) {μ: Eval AP} : (μ ⊨ₚ p2) → (μ ⊨ₚ p1) := (h.forall_iff μ).mpr

@[scoped grind ., refl]
theorem refl (p: Formula AP) : (p ≡ₚ p) := by
  unfold SemEquiv
  intro _; rfl

@[scoped grind →, symm]
theorem symm (p1 p2: Formula AP) (h: (p1 ≡ₚ p2)) : p2 ≡ₚ p1 := by
  revert h
  unfold SemEquiv
  intro h μ
  symm
  exact @h μ

@[scoped grind →]
theorem trans (p1 p2 p3: Formula AP)
  (h1: (p1 ≡ₚ p2)) (h2: (p2 ≡ₚ p3))
  : p1 ≡ₚ p3 := by
  revert h1 h2
  unfold SemEquiv
  intro h1 h2 μ
  specialize @h1 μ
  specialize @h2 μ
  exact Iff.trans h1 h2

variable (AP) in
theorem eqv : Equivalence (· ≡ₚ · : Formula AP → Formula AP → Prop) where
  refl := SemEquiv.refl
  symm := SemEquiv.symm _ _
  trans := SemEquiv.trans _ _ _

instance : IsEquiv (Formula AP) (· ≡ₚ ·) := IsEquiv.of_equivalence (SemEquiv.eqv AP)


variable (AP) in
@[reducible]
def toSetoid : Setoid (Formula AP) where
  r := SemEquiv AP
  iseqv := SemEquiv.eqv AP


open scoped IsSat

@[scoped grind .]
theorem neg_neg (p: Formula AP)
  : ¬ₚ¬ₚp ≡ₚ p := by
  grind only [= semEquiv_def, → symm, = IsSat.neg_iff]

@[scoped grind .]
theorem id_or (p: Formula AP)
  : p ∨ₚ p ≡ₚ p := by
  grind only [= semEquiv_def, → symm, = IsSat.or_iff]

@[scoped grind .]
theorem id_and (p: Formula AP)
  : p ∧ₚ p ≡ₚ p := by
  grind only [= semEquiv_def, → symm, = IsSat.and_iff]

@[scoped grind .]
theorem absorb_and (p1 p2: Formula AP)
  : p1 ∧ₚ (p2 ∨ₚ p1) ≡ₚ p1 := by
  grind only [= semEquiv_def, → symm, = IsSat.and_iff, = IsSat.or_iff]

@[scoped grind .]
theorem absorb_or (p1 p2: Formula AP)
  : p1 ∨ₚ (p2 ∧ₚ p1) ≡ₚ p1 := by
  grind only [= semEquiv_def, → symm, = IsSat.or_iff, = IsSat.and_iff]

@[scoped grind .]
theorem comm_or (p1 p2: Formula AP)
  : p1 ∨ₚ p2 ≡ₚ p2 ∨ₚ p1 := by
  grind only [= semEquiv_def, → symm, = IsSat.or_iff]

@[scoped grind .]
theorem comm_and (p1 p2: Formula AP)
  : p1 ∧ₚ p2 ≡ₚ p2 ∧ₚ p1 := by
  grind only [= semEquiv_def, → symm, = IsSat.and_iff]

@[scoped grind .]
theorem assoc_and (p1 p2 p3: Formula AP)
  : p1 ∧ₚ (p2 ∧ₚ p3) ≡ₚ (p1 ∧ₚ p2) ∧ₚ p3 := by
  grind only [= semEquiv_def, → symm, = IsSat.and_iff]

@[scoped grind .]
theorem assoc_or (p1 p2 p3: Formula AP)
  : p1 ∨ₚ (p2 ∨ₚ p3) ≡ₚ (p1 ∨ₚ p2) ∨ₚ p3 := by
  grind only [= semEquiv_def, → symm, = IsSat.or_iff]

@[scoped grind .]
theorem demorgan_and (p1 p2: Formula AP)
  : ¬ₚ(p1 ∧ₚ p2) ≡ₚ (¬ₚp1 ∨ₚ ¬ₚp2) := by
  grind only [= semEquiv_def, → symm, = IsSat.neg_iff, = IsSat.or_iff, = IsSat.and_iff]

@[scoped grind .]
theorem demorgan_or (p1 p2: Formula AP)
  : ¬ₚ(p1 ∨ₚ p2) ≡ₚ (¬ₚp1 ∧ₚ ¬ₚp2) := by
  grind only [= semEquiv_def, → symm, = IsSat.neg_iff, = IsSat.and_iff, = IsSat.or_iff]

@[scoped grind .]
theorem dist_or (p1 p2 p3: Formula AP)
  : p1 ∨ₚ (p2 ∧ₚ p3) ≡ₚ (p1 ∨ₚ p2) ∧ₚ (p1 ∨ₚ p3) := by
  grind

@[scoped grind .]
theorem dist_and (p1 p2 p3: Formula AP)
  : p1 ∧ₚ (p2 ∨ₚ p3) ≡ₚ (p1 ∧ₚ p2) ∨ₚ (p1 ∧ₚ p3) := by
  grind

@[scoped grind =]
theorem iterAnd_nil : ⋀ₚ ([]: List (Formula AP)) ≡ₚ (.true) := by
  unfold Formula.iterAnd
  rfl

@[scoped grind .]
theorem iterAnd_cons (p: Formula AP) (ps: List (Formula AP))
  : ⋀ₚ (p :: ps) ≡ₚ (p ∧ₚ (⋀ₚ ps)) := by
  dsimp [Formula.iterAnd]
  rfl

@[scoped grind =]
theorem iterOr_nil : ⋁ₚ ([]: List (Formula AP)) ≡ₚ (.false) := by
  unfold Formula.iterOr
  rfl

@[scoped grind .]
theorem iterOr_cons (p: Formula AP) (ps: List (Formula AP))
  : ⋁ₚ (p :: ps) ≡ₚ (p ∨ₚ (⋁ₚ ps)) := by
  dsimp [Formula.iterOr]
  rfl

end SemEquiv


end Nemonuri.PropositionalLogics

end
