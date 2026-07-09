module

public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace Nemonuri.PropositionalLogics


inductive FormulaRaw (Atom: Type _) where
  | true
  | atom (x: Atom)
  | neg (x: FormulaRaw Atom)
  | and (x: FormulaRaw Atom) (y: FormulaRaw Atom)

@[mk_iff]
inductive IsFormula {Atom: Type _} (AP: Finset Atom) : (FormulaRaw Atom) → Prop where
  | true : IsFormula AP (.true)
  | atom (x: Atom) (h: x ∈ AP) : IsFormula AP (.atom x)
  | neg (x: FormulaRaw Atom) (hx: IsFormula AP x) : IsFormula AP (.neg x)
  | and (x: FormulaRaw Atom) (y: FormulaRaw Atom)
        (hx: IsFormula AP x) (hy: IsFormula AP y) : IsFormula AP (.and x y)

@[ext]
structure Formula {Atom: Type _} (AP: Finset Atom) where
  raw: FormulaRaw Atom
  is_formula: IsFormula AP raw



namespace Formula

variable {Atom: Type _} {AP: Finset Atom}

protected def mk' (AP) (x: FormulaRaw Atom) (h: IsFormula AP x) : Formula AP := @Formula.mk _ AP x h

protected def true (AP: Finset Atom) : Formula AP := ⟨.true, .true⟩

protected def atom (AP: Finset Atom) (x: AP) : Formula AP := ⟨.atom x.val, .atom x.val x.property⟩

protected def neg (x: Formula AP) : Formula AP := ⟨.neg x.raw, .neg x.raw x.is_formula⟩

protected def and (x y: Formula AP) : Formula AP := ⟨.and x.raw y.raw, .and x.raw y.raw x.is_formula y.is_formula⟩

@[elab_as_elim, induction_eliminator]
protected def recAlt
  {motive : Formula AP → Sort _}
  (true : motive <| Formula.true AP)
  (atom : (x: AP) → motive <| Formula.atom AP x)
  (neg : (x: Formula AP) → motive <| Formula.neg x)
  (and : (x y: Formula AP) → motive <| Formula.and x y)
  (t: Formula AP)
  : motive t :=
  let ⟨raw, is_formula⟩ := t
  match raw with
  | .true => true
  | .atom x => atom ⟨x, by cases is_formula; assumption⟩
  | .neg x => neg (.mk' AP x (by cases is_formula; assumption))
  | .and x y => and (.mk' AP x (by cases is_formula; assumption)) (.mk' AP y (by cases is_formula; assumption))


inductive Splitted (AP: Finset Atom) : Formula AP → Type _ where
  | true : Splitted AP (.true AP)
  | atom (x: AP) : Splitted AP (.atom AP x)
  | neg (x: Formula AP) : Splitted AP (.neg x)
  | and (x y: Formula AP) : Splitted AP (.and x y)

def split (x: Formula AP) : Splitted AP x :=
  Formula.recAlt Splitted.true Splitted.atom Splitted.neg Splitted.and x

protected def or (x y: Formula AP) : Formula AP := .and (.neg x) (.neg y) |> .neg

protected def imp (x y: Formula AP) : Formula AP := .or (.neg x) y

protected def equiv (x y: Formula AP) : Formula AP := .or (.and (.neg x) (.neg y)) (.and x y)


section Notation

syntax:40 " ¬ₚ" term:40 : term
syntax:36 term:37 " ∧ₚ " term:36 : term
syntax:35 term:36 " ∨ₚ " term:35 : term
syntax:31 term:32 " →ₚ " term:31 : term
syntax:30 term:31 " ↔ₚ " term:30 : term

macro_rules
  | `(¬ₚ$x) => ``(Formula.neg $x)
  | `($x ∧ₚ $y) => ``(Formula.and $x $y)
  | `($x ∨ₚ $y) => ``(Formula.or $x $y)
  | `($x →ₚ $y) => ``(Formula.imp $x $y)
  | `($x ↔ₚ $y) => ``(Formula.equiv $x $y)

end Notation



structure Eval (AP: Finset Atom) where
  eval : AP → Bool

instance : FunLike (Eval AP) AP Bool where
  coe μ := μ.eval
  coe_injective μ1 μ2 := by cases μ1; cases μ2; simp


structure SatRelRaw (AP: Finset Atom) where
  ofRel :: rel : Eval AP → Formula AP → Prop

instance : FunLike (SatRelRaw AP) (Eval AP) (Formula AP → Prop) where
  coe x := x.rel
  coe_injective x1 x2 := by cases x1; cases x2; simp

@[mk_iff]
structure IsSatRel (AP: Finset Atom) (raw: SatRelRaw AP) : Prop where
  true : ∀μ, raw μ (.true AP)
  atom (a: AP) : ∀μ, raw μ (.atom AP a) ↔ (μ a = .true)
  neg (x: Formula AP) : ∀μ, raw μ (.neg x) ↔ (¬raw μ x)
  and (x y: Formula AP) : ∀μ, raw μ (.and x y) ↔ (raw μ x ∧ raw μ y)

structure SatRel (AP: Finset Atom) where
  raw: SatRelRaw AP
  is_sat_rel: IsSatRel AP raw

instance : FunLike (SatRel AP) (Eval AP) (Formula AP → Prop) where
  coe x := x.raw
  coe_injective x1 x2 := by cases x1; cases x2; simp




namespace SatRel

variable (sr: SatRel AP) (μ: Eval AP)

theorem app_eq_raw_app
  : sr μ = sr.raw μ :=
  rfl

abbrev IsSat (p: Formula AP) : Prop := sr μ p

namespace IsSat

@[grind .]
theorem true_intro
  : sr.IsSat μ (.true AP) := by
  simp only [IsSat, app_eq_raw_app]
  exact sr.is_sat_rel.true μ

@[grind =]
theorem atom_iff (a: AP)
  : sr.IsSat μ (.atom AP a) ↔ μ a = .true := by
  simp only [IsSat, app_eq_raw_app]
  rw [sr.is_sat_rel.atom]

@[grind =]
theorem neg_iff (p: Formula AP)
  : sr.IsSat μ (.neg p) ↔ ¬sr.IsSat μ p := by
  simp only [IsSat, app_eq_raw_app _ μ]
  rw [sr.is_sat_rel.neg]

@[grind =]
theorem and_iff (p1 p2: Formula AP)
  : sr.IsSat μ (.and p1 p2) ↔ (sr.IsSat μ p1) ∧ (sr.IsSat μ p2) := by
  simp only [IsSat, app_eq_raw_app _ μ]
  rw [sr.is_sat_rel.and]

@[grind =]
theorem or_iff (p1 p2: Formula AP)
  : sr.IsSat μ (.or p1 p2) ↔ (sr.IsSat μ p1) ∨ (sr.IsSat μ p2) := by
  simp only [Formula.or]
  grind

theorem imp_iff_or (p1 p2: Formula AP)
  : sr.IsSat μ (.imp p1 p2) ↔ ¬(sr.IsSat μ p1) ∨ (sr.IsSat μ p2) := by
  simp only [Formula.imp]
  grind

@[grind =]
theorem imp_iff_imp (p1 p2: Formula AP)
  : sr.IsSat μ (.imp p1 p2) ↔ ((sr.IsSat μ p1) → (sr.IsSat μ p2)) := by
  simp only [imp_iff_or]
  grind only

end IsSat


syntax:25 term:26 " ⊨ₚ{" term "} " term:25 : term

macro_rules
  | `($μ ⊨ₚ{ $sr } $φ ) => ``(SatRel.IsSat $sr $μ $φ)


class HasSatRelAt (AP: Finset Atom) (μ: Eval AP) (p: Formula AP) where
  satRel: SatRel AP

abbrev HasSatRel (Atom: Type _) : Type _ := (AP: Finset Atom) → (μ: Eval AP) → (p: Formula AP) → HasSatRelAt AP μ p


syntax:25 term:26 " ⊨ₚ " term:25 : term

macro_rules
  | `($μ ⊨ₚ $φ) => ``($μ ⊨ₚ{ HasSatRelAt.satRel $μ $φ } $φ )





/-
theorem IsSat.imp_iff_or (p1 p2: Formula AP)
  : sr.IsSat μ (.imp p1 p2) ↔ ¬(sr.IsSat μ p1) ∨ (sr.IsSat μ p2) := by
  --rcases sr with ⟨raw, is_sat_rel⟩
  simp only [Formula.imp]
  simp only [IsSat.or_iff]
-/

end SatRel


end Formula






end Nemonuri.PropositionalLogics

end
