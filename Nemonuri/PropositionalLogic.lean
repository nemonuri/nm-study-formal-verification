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

variable {Atom: Type _} (AP: Finset Atom)

protected def mk' (x: FormulaRaw Atom) (h: IsFormula AP x) : Formula AP := @Formula.mk _ AP x h

protected def true : Formula AP := ⟨.true, .true⟩

protected def atom (x: Atom) (h: x ∈ AP) : Formula AP := ⟨.atom x, .atom x h⟩

protected def neg (x: Formula AP) : Formula AP := ⟨.neg x.raw, .neg x.raw x.is_formula⟩

protected def and (x y: Formula AP) : Formula AP := ⟨.and x.raw y.raw, .and x.raw y.raw x.is_formula y.is_formula⟩

@[elab_as_elim, induction_eliminator]
protected def recAlt
  {motive : Formula AP → Sort _}
  (true : motive <| Formula.true AP)
  (atom : (x: Atom) → (h: x ∈ AP) → motive <| Formula.atom AP x h)
  (neg : (x: Formula AP) → motive <| Formula.neg AP x)
  (and : (x y: Formula AP) → motive <| Formula.and AP x y)
  (t: Formula AP)
  : motive t :=
  let ⟨raw, is_formula⟩ := t
  match raw with
  | .true => true
  | .atom x => atom x (by cases is_formula; assumption)
  | .neg x => neg (.mk' AP x (by cases is_formula; assumption))
  | .and x y => and (.mk' AP x (by cases is_formula; assumption)) (.mk' AP y (by cases is_formula; assumption))


inductive Splitted {Atom: Type _} (AP: Finset Atom) : Formula AP → Type _ where
  | true : Splitted AP (.true AP)
  | atom (x: Atom) (h: x ∈ AP) : Splitted AP (.atom AP x h)
  | neg (x: Formula AP) : Splitted AP (.neg AP x)
  | and (x y: Formula AP) : Splitted AP (.and AP x y)

def split (x: Formula AP) : Splitted AP x :=
  Formula.recAlt AP Splitted.true Splitted.atom Splitted.neg Splitted.and x




end Formula



end Nemonuri.PropositionalLogics

end
