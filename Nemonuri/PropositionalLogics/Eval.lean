module

public import Nemonuri.PropositionalLogics.Formula


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], A.3 Propositional Logic, p.915

-/


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics


structure Eval (AP: Type _) where ofIndicator :: toIndicator : AP → Bool
  --eval : AP → Bool


namespace Eval

variable {AP: Type*}-- [Fintype AP]

@[pl_simp]
protected abbrev eval (e: Eval AP) : AP → Bool := e.toIndicator

variable (AP) in
def equivToIndicator : Eval AP ≃ (AP → Bool) where
  toFun e := e.toIndicator
  invFun ind := Eval.ofIndicator ind


instance : FunLike (Eval AP) AP Bool where
  coe μ := μ.eval
  coe_injective μ1 μ2 := by cases μ1; cases μ2; simp

@[defeq, pl_simp]
theorem app_eq_eval_app (μ: Eval AP) (a: AP) : μ a = μ.eval a := by rfl

def evalFormula (μ: Eval AP) (p: Formula AP) : Bool :=
  match p with
  | .true => .true
  | .atom ap => μ ap
  | .neg p => !(μ.evalFormula p)
  | .and p1 p2 => (μ.evalFormula p1) && (μ.evalFormula p2)

section EvalFormulaSection

variable {μ: Eval AP} --{p: Formula AP}

@[defeq, pl_simp]
theorem evalFormula_true : μ.evalFormula .true = .true := rfl

@[defeq, pl_simp]
theorem evalFormula_atom {ap: AP} : μ.evalFormula (.atom ap) = μ.toIndicator ap := rfl

@[defeq, pl_simp]
theorem evalFormula_neg {p: Formula AP} : μ.evalFormula (.neg p) = !(μ.evalFormula p) := rfl

@[defeq, pl_simp]
theorem evalFormula_and {p1 p2: Formula AP} : μ.evalFormula (.and p1 p2) = ((μ.evalFormula p1) && (μ.evalFormula p2)) := rfl

end EvalFormulaSection


open Formula in
theorem evalFormula_eq_evalToBool_of_ap_empty [IsEmpty AP] {μ: Eval AP} {p: Formula AP}
  : μ.evalFormula p = p.evalToBool (p.hasAtom_eq_false_of_ap_empty) := by
  have lm1 := p.hasAtom_eq_false_of_ap_empty
  have lm2 := p.evalToBool?_isSome_of_hasAtom_eq_false lm1 |> Option.isSome_iff_exists.mp
  rcases lm2 with ⟨val, lm2⟩
  rcases p with _ | ap | p | ⟨p1, p2⟩
  · dsimp [evalFormula, evalToBool, evalToBool?]
  · revert ap; simp only [IsEmpty.forall_iff]
  · dsimp [evalFormula]
    have lm3 := @evalFormula_eq_evalToBool_of_ap_empty _ μ p |>.symm
    rewrite [p.evalToBool_eq_iff_evalToBool?_eq_some] at lm3
    have lm4 := lm2
    dsimp [evalToBool?] at lm4
    simp [lm3] at lm4
    symm
    rw [p.neg.evalToBool_eq_iff_evalToBool?_eq_some, lm2, lm4]
    simp
  · obtain ⟨lm1_1, lm1_2⟩ := and_hasAtom_eq_false_iff_hasAtom_eq_false_and.mp lm1
    clear lm1
    have lm3_1 := @evalFormula_eq_evalToBool_of_ap_empty _ μ p1 |>.symm
    have lm3_2 := @evalFormula_eq_evalToBool_of_ap_empty _ μ p2 |>.symm
    rewrite [evalToBool_eq_iff_evalToBool?_eq_some] at lm3_1 lm3_2
    have lm4 := lm2
    dsimp [evalToBool?] at lm4
    rewrite [lm3_1, lm3_2] at lm4
    simp at lm4
    dsimp [evalFormula]
    symm
    rw [lm4, evalToBool_eq_iff_evalToBool?_eq_some]
    exact lm2

def IsTrueFormula (e: Eval AP) (fml: Formula AP) : Prop := e.evalFormula fml = .true

@[defeq]
theorem isTrueFormula_def {e: Eval AP} {fml: Formula AP} : e.IsTrueFormula fml = (e.evalFormula fml = .true) := rfl

instance (μ: Eval AP) (fml: Formula AP) : Decidable (μ.IsTrueFormula fml) := decidable_of_decidable_of_eq isTrueFormula_def.symm

end Eval

/-
abbrev Indicator (AP: Type _) [Fintype AP] : Type _ := AP → Bool

@[defeq]
theorem indicator_def {AP: Type _} [Fintype AP] : Indicator AP = (AP → Bool) := rfl

namespace Indicator

variable {AP: Type _} [Fintype AP]

def mk (f: AP → Bool) : Indicator AP := f

def fn (ind: Indicator AP) : AP → Bool := ind

@[defeq, simp]
theorem mk_fn_eq {f: AP → Bool} : (mk f).fn = f := rfl

@[defeq, simp]
theorem mk_eq {f: AP → Bool} {ap: AP} : (mk f) ap = f ap := rfl


def evalFormulaToBool (ind: Indicator AP) (p: Formula AP) : Bool :=
  match p with
  | .true => .true
  | .atom ap => ind.fn ap
  | .neg p => !(ind.evalFormulaToBool p)
  | .and p1 p2 => (ind.evalFormulaToBool p1) && (ind.evalFormulaToBool p2)


open Formula in
theorem evalFormulaToBool_eq_evalToBool_of_ap_empty [IsEmpty AP] {ind: Indicator AP} {p: Formula AP}
  : ind.evalFormulaToBool p = p.evalToBool (p.hasAtom_eq_false_of_ap_empty) := by
  have lm1 := p.hasAtom_eq_false_of_ap_empty
  have lm2 := p.evalToBool?_isSome_of_hasAtom_eq_false lm1 |> Option.isSome_iff_exists.mp
  rcases lm2 with ⟨val, lm2⟩
  rcases p with _ | ap | p | ⟨p1, p2⟩
  · dsimp [evalFormulaToBool, evalToBool, evalToBool?]
  · revert ap; simp only [IsEmpty.forall_iff]
  · dsimp [evalFormulaToBool]
    have lm3 := @evalFormulaToBool_eq_evalToBool_of_ap_empty _ ind p |>.symm
    rewrite [p.evalToBool_eq_iff_evalToBool?_eq_some] at lm3
    have lm4 := lm2
    dsimp [evalToBool?] at lm4
    simp [lm3] at lm4
    symm
    rw [p.neg.evalToBool_eq_iff_evalToBool?_eq_some, lm2, lm4]
    simp
  · obtain ⟨lm1_1, lm1_2⟩ := and_hasAtom_eq_false_iff_hasAtom_eq_false_and.mp lm1
    clear lm1
    have lm3_1 := @evalFormulaToBool_eq_evalToBool_of_ap_empty _ ind p1 |>.symm
    have lm3_2 := @evalFormulaToBool_eq_evalToBool_of_ap_empty _ ind p2 |>.symm
    rewrite [evalToBool_eq_iff_evalToBool?_eq_some] at lm3_1 lm3_2
    have lm4 := lm2
    dsimp [evalToBool?] at lm4
    rewrite [lm3_1, lm3_2] at lm4
    simp at lm4
    dsimp [evalFormulaToBool]
    symm
    rw [lm4, evalToBool_eq_iff_evalToBool?_eq_some]
    exact lm2


structure AreEvalToTrue (ind: Indicator AP) (p: Formula AP) : Prop where
  intro :: eq_true : evalFormulaToBool ind p = .true

namespace AreEvalToTrue

variable {ind: Indicator AP} {p: Formula AP}

theorem eq_true_iff : (evalFormulaToBool ind p = .true) ↔ (AreEvalToTrue ind p) := by
  constructor
  · intro lm1
    exact .intro lm1
  · rintro ⟨lm1⟩
    exact lm1

end AreEvalToTrue

end Indicator
-/

end Nemonuri.PropositionalLogics
