module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Setoid.Basic

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], A.3 Propositional Logic, p.915

-/

@[expose] public section

namespace Nemonuri.PropositionalLogics


inductive Formula (AP: Type _) [Fintype AP] where
  | true
  | atom (x: AP)
  | neg (x: Formula AP)
  | and (x: Formula AP) (y: Formula AP)

/-
@[mk_iff]
inductive IsFormula (AP: Type _) [Fintype AP] : (FormulaRaw AP) → Prop where
  | true : IsFormula AP (.true)
  | atom (x: AP) : IsFormula AP (.atom x)
  | neg (x: FormulaRaw AP) (hx: IsFormula AP x) : IsFormula AP (.neg x)
  | and (x: FormulaRaw AP) (y: FormulaRaw AP)
        (hx: IsFormula AP x) (hy: IsFormula AP y) : IsFormula AP (.and x y)

@[ext]
structure Formula (AP: Type _) [Fintype AP] where
  raw: FormulaRaw AP
  valid: IsFormula AP raw
-/


namespace Formula

variable {AP: Type _} [Fintype AP]

instance toNonempty : Nonempty (Formula AP) := .intro .true

theorem ne_atom_of_empty_ap [IsEmpty AP] {p: Formula AP} {ap: AP} : (p ≠ .atom ap) := by
  intro lm1
  cases p <;> try simp at lm1
  exact (inferInstance: IsEmpty AP).false ap

theorem exists_eq_atom_iff_nonempty : (∃(p: Formula AP), ∃(ap: AP), p = .atom ap) ↔ Nonempty AP := by
  constructor
  · rintro ⟨p, ap, lm1⟩
    exact .intro ap
  · rintro ⟨ap⟩
    exists .atom ap
    exists ap

def hasAtom : Formula AP → Bool
  | .true => .false
  | .atom _ => .true
  | .neg p => hasAtom p
  | .and p1 p2 => (hasAtom p1) || (hasAtom p2)

@[simp]
theorem and_hasAtom_eq_false_iff_hasAtom_eq_false_and {p1 p2: Formula AP}
  : ((p1.and p2).hasAtom = .false) ↔ (p1.hasAtom = false) ∧ (p2.hasAtom = false) := by
  simp [hasAtom]



def collectAtom [DecidableEq AP] : Formula AP → Finset AP
  | .true => ∅
  | .atom ap => {ap}
  | .neg p => collectAtom p
  | .and p1 p2 => (collectAtom p1) ∪ (collectAtom p2)


theorem hasAtom_eq_true_iff_collectAtom_nonempty [DecidableEq AP] {p: Formula AP}
  : p.hasAtom = .true ↔ p.collectAtom.Nonempty := by
  rcases p with _ | ap | p | ⟨p1, p2⟩
  · dsimp [hasAtom, collectAtom]; simp
  · dsimp [hasAtom, collectAtom]; simp
  · dsimp [hasAtom, collectAtom]
    exact @p.hasAtom_eq_true_iff_collectAtom_nonempty _
  · dsimp [hasAtom, collectAtom]
    simp
    have lm1 := @p1.hasAtom_eq_true_iff_collectAtom_nonempty _
    have lm2 := @p2.hasAtom_eq_true_iff_collectAtom_nonempty _
    rw [lm1, lm2]


theorem hasAtom_eq_false_of_ap_empty [IsEmpty AP] {p: Formula AP} : p.hasAtom = .false := by
  by_contra lm1
  simp at lm1
  let deqAP : DecidableEq AP := Classical.typeDecidableEq AP
  have lm2 := p.hasAtom_eq_true_iff_collectAtom_nonempty
  replace lm2 := lm2.mp lm1 |> Finset.nonempty_def.mp
  rcases lm2 with ⟨ap, lm2⟩
  exact (inferInstance : IsEmpty AP).false ap


def evalToBool? (p: Formula AP) : Option Bool := do
  match p with
  | .true => return .true
  | .atom _ => .none
  | .neg p => return !(← p.evalToBool?)
  | .and p1 p2 => return (← p1.evalToBool?) && (← p2.evalToBool?)

theorem evalToBool?_isSome_of_hasAtom_eq_false (p: Formula AP) (req: p.hasAtom = .false) : p.evalToBool?.isSome = .true := by
  rcases p with _ | ap | p | ⟨p1, p2⟩
  · dsimp [evalToBool?]
  · dsimp [hasAtom] at req
    simp at req
  · dsimp [hasAtom] at req
    dsimp [evalToBool?]
    cases lm1: p.evalToBool?
    · simp
      have lm2 := p.evalToBool?_isSome_of_hasAtom_eq_false req
      simp [lm1] at lm2
    · simp
  · dsimp [hasAtom] at req
    dsimp [evalToBool?]
    simp at req
    rcases req with ⟨req1, req2⟩
    cases lm1: p1.evalToBool?
    · have lm2 := p1.evalToBool?_isSome_of_hasAtom_eq_false req1
      simp [lm1] at lm2
    · simp
      cases lm2: p2.evalToBool?
      · have lm3 := p2.evalToBool?_isSome_of_hasAtom_eq_false req2
        simp [lm2] at lm3
      · simp

def evalToBool (p: Formula AP) (req: p.hasAtom = .false) : Bool :=
  match lm1: p.evalToBool? with
  | .some val => val
  | .none => absurd lm1 (by
      have lm2 := p.evalToBool?_isSome_of_hasAtom_eq_false req
      simp [lm1] at lm2 )

theorem evalToBool_eq_iff_evalToBool?_eq_some {p: Formula AP} (req: p.hasAtom = .false) {b: Bool}
  : (p.evalToBool req = b) ↔ (p.evalToBool? = .some b) := by
  have lm1 := p.evalToBool?_isSome_of_hasAtom_eq_false req
  dsimp [evalToBool]
  split <;> (rename_i lm2; simp [lm2] at lm1)
  rw [lm2]
  exact Option.some_inj.symm


/-
protected def mk' (AP: Type _) [Fintype AP] (x: FormulaRaw AP) (h: IsFormula AP x) : Formula AP := @Formula.mk AP _ x h

@[match_pattern]
protected def true (AP: Type _) [Fintype AP] : Formula AP := ⟨.true, .true⟩

@[match_pattern]
protected def atom (x: AP) : Formula AP := ⟨.atom x, .atom x⟩

@[match_pattern]
protected def neg (x: Formula AP) : Formula AP := ⟨.neg x.raw, .neg x.raw x.valid⟩

@[match_pattern]
protected def and (x y: Formula AP) : Formula AP := ⟨.and x.raw y.raw, .and x.raw y.raw x.valid y.valid⟩

@[elab_as_elim]
protected def recAlt
  {motive : Formula AP → Sort _}
  (true : motive <| Formula.true AP)
  (atom : (x: AP) → motive <| Formula.atom x)
  (neg : (x: Formula AP) → motive <| Formula.neg x)
  (and : (x y: Formula AP) → motive <| Formula.and x y)
  (t: Formula AP)
  : motive t :=
  let ⟨raw, valid⟩ := t
  match raw with
  | .true => true
  | .atom x => atom x
  | .neg x => neg (.mk' AP x (by cases valid; assumption))
  | .and x y => and (.mk' AP x (by cases valid; assumption)) (.mk' AP y (by cases valid; assumption))
-/

/-
inductive Splitted (AP: Finset Atom) : Formula AP → Type _ where
  | true : Splitted AP (.true AP)
  | atom (x: AP) : Splitted AP (.atom AP x)
  | neg (x: Formula AP) : Splitted AP (.neg x)
  | and (x y: Formula AP) : Splitted AP (.and x y)

def split (x: Formula AP) : Splitted AP x :=
  Formula.recAlt Splitted.true Splitted.atom Splitted.neg Splitted.and x
-/

protected def or (x y: Formula AP) : Formula AP := .and (.neg x) (.neg y) |> .neg

protected def imp (x y: Formula AP) : Formula AP := .or (.neg x) y

protected def eqv (x y: Formula AP) : Formula AP := .or (.and (.neg x) (.neg y)) (.and x y)

protected def false : Formula AP := .neg (.true)

def iterAnd (xs: List (Formula AP)) : Formula AP :=
  match xs with
  | [] => (.true)
  | hd::tl => .and hd (iterAnd tl)

def iterOr (xs: List (Formula AP)) : Formula AP :=
  match xs with
  | [] => (.false)
  | hd::tl => .or hd (iterOr tl)


section Notation

syntax:42 " ¬ₚ" term:42 : term
syntax:36 term:37 " ∧ₚ " term:36 : term
syntax:35 term:36 " ∨ₚ " term:35 : term
syntax:31 term:32 " →ₚ " term:31 : term
syntax:30 term:31 " ↔ₚ " term:30 : term
syntax:41 " ⋀ₚ" term:41 : term
syntax:41 " ⋁ₚ" term:41 : term

macro_rules
  | `(¬ₚ$x) => ``(Formula.neg $x)
  | `($x ∧ₚ $y) => ``(Formula.and $x $y)
  | `($x ∨ₚ $y) => ``(Formula.or $x $y)
  | `($x →ₚ $y) => ``(Formula.imp $x $y)
  | `($x ↔ₚ $y) => ``(Formula.equiv $x $y)
  | `(⋀ₚ$xs) => ``(iterAnd $xs)
  | `(⋁ₚ$xs) => ``(iterOr $xs)

end Notation

def atomTuple (as: List AP) : Formula AP := ⋀ₚ (as.map (Formula.atom))

end Formula


structure Eval (AP: Type _) [Fintype AP] where
  eval : AP → Bool

namespace Eval

variable {AP: Type _} [Fintype AP]

instance : FunLike (Eval AP) AP Bool where
  coe μ := μ.eval
  coe_injective μ1 μ2 := by cases μ1; cases μ2; simp

theorem app_eq_eval_app (μ: Eval AP) (a: AP) : μ a = μ.eval a := by rfl

end Eval

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



/-
    have lm3 := @evalFormulaToBool_eq_evalToBool_of_ap_empty _ ind p |>.symm
    rewrite [p.evalToBool_eq_iff_evalToBool?_eq_some] at lm3
    symm
    rw [p.neg.evalToBool_eq_iff_evalToBool?_eq_some, lm2]
-/
/-
    simp
    have lm3 := @evalFormulaToBool_eq_evalToBool_of_ap_empty _ ind p
    refine Eq.trans lm3 ?_
    obtain ⟨_, lm4⟩ := p.evalToBool?_isSome_of_hasAtom_eq_false lm1 |> Option.isSome_iff_exists.mp
    dsimp [evalToBool] at lm3
    split at lm3 <;> (rename_i lm5; simp [lm4] at lm5)
-/

    --dsimp [evalToBool]




scoped instance [DecidableEq AP] : Fintype (AP → Bool) := Pi.instFintype

instance toFintype [DecidableEq AP] : Fintype (Indicator AP) := inferInstanceAs (Fintype (AP → Bool))

instance toFinite : Finite (Indicator AP) := letI := Classical.typeDecidableEq AP; Finite.of_fintype (Indicator AP)

instance toNonempty : Nonempty (Indicator AP) := inferInstanceAs (Nonempty (AP → Bool))

instance uniqueOfIsEmpty [IsEmpty AP] : Unique (Indicator AP) := Pi.uniqueOfIsEmpty (fun _ => Bool)


def forallRightEquiv (α: Sort _) : (α → Indicator AP) ≃ (α → AP → Bool) where
  toFun x := x
  invFun x := x

@[simps]
def forallRightEquivOfEquiv {Ind: Sort _} (eqv: Indicator AP ≃ Ind) (α: Sort _) : (α → Indicator AP) ≃ (α → Ind) where
  toFun f a := eqv (f a)
  invFun f a := eqv.symm (f a)
  left_inv := by intro _; simp
  right_inv := by intro _; simp

def equivToEval : Indicator AP ≃ Eval AP where
  toFun := Eval.mk
  invFun := Eval.eval


def toFinset (ind: Indicator AP) : Finset AP := { ap: AP | ind.fn ap = .true }

section OfFinset

variable [DecidableEq AP]

def ofFinset (fs: Finset AP) : Indicator AP := .mk (fun ap => decide (ap ∈ fs))

theorem ofFinset_toFinset_leftInverse : Function.LeftInverse (@ofFinset AP _ _) toFinset := by
  dsimp [Function.LeftInverse, ofFinset, toFinset]
  dsimp [Indicator, fn, mk]
  simp

theorem ofFinset_toFinset_rightInverse : Function.RightInverse (@ofFinset AP _ _) toFinset := by
  dsimp [Function.RightInverse, Function.LeftInverse, ofFinset, toFinset]
  simp

@[simps]
def equivToFinset : Indicator AP ≃ Finset AP where
  toFun := toFinset
  invFun := ofFinset
  left_inv := ofFinset_toFinset_leftInverse
  right_inv := ofFinset_toFinset_rightInverse


end OfFinset

end Indicator


namespace Eval

variable {AP: Type _} [Fintype AP]

instance toFintype [DecidableEq AP] : Fintype (Eval AP) := Fintype.ofEquiv (Indicator AP) Indicator.equivToEval

instance to_finite : Finite (Eval AP) := letI := Classical.typeDecidableEq AP; Finite.of_fintype (Eval AP)

instance to_nonempty : Nonempty (Eval AP) := Equiv.nonempty Indicator.equivToEval.symm

instance uniqueOfAPEmpty [IsEmpty AP] : Unique (Eval AP) := Equiv.unique Indicator.equivToEval.symm


theorem all_eq_of_ap_empty [IsEmpty AP] {ev1 ev2: Eval AP} : ev1 = ev2 := (inferInstance: Unique (Eval AP)).instSubsingleton.allEq ev1 ev2


theorem subset_finite {ss: Set (Eval AP)} : ss.Finite := by
  have lm1 : Finite (Eval AP) := to_finite
  rw [← Set.finite_coe_iff]
  exact Subtype.finite



end Eval




class EvalLike (E: Type _) (AP: outParam <| Type _) [Fintype AP] where
  protected coe (e: E) : Eval AP
  coe_injective : Function.Injective coe
  --coe_surjective : Function.Surjective coe

namespace EvalLike

attribute [coe] EvalLike.coe

variable {E: Type _} {AP: Type _} [Fintype AP] [EvalLike E AP]

instance : CoeOut E (Eval AP) where coe := EvalLike.coe

abbrev toIndicator (e: E) : Indicator AP := .mk ((e: Eval AP) : AP → Bool)

def toIndicator_def {e: E} : (toIndicator e) = .mk ((e: Eval AP).eval) := rfl


abbrev AreEvalToTrueAt (E AP: Type _) [Fintype AP] [EvalLike E AP] : E → Formula AP → Prop := Indicator.AreEvalToTrue ∘ toIndicator

@[defeq]
theorem areEvalToTrueAt_eq_areEvalToTrue {e: E} {p: Formula AP} : AreEvalToTrueAt E AP e p = (toIndicator e).AreEvalToTrue p := rfl


instance finite_of_carrier : Finite E := Finite.of_injective EvalLike.coe EvalLike.coe_injective

instance coe_finite : Finite (E → (Eval AP)) := Pi.finite

instance to_finite : Finite (EvalLike E AP) := by
  let invMk (e: EvalLike E AP) : E → (Eval AP) := e.coe
  refine Finite.of_injective invMk ?_
  subst invMk
  rintro ⟨el1_1, el1_2⟩ ⟨el2_1, el2_2⟩
  simp
  intro lm1
  congr


instance coeUniqueOfAPEmpty [IsEmpty AP] : Unique (E → (Eval AP)) := Pi.unique


theorem coe_eq_of_ap_empty [IsEmpty AP] {E2: Type _} [EvalLike E2 AP] {e: E} (e2: E2) : (e: Eval AP) = (e2: Eval AP) := Eval.all_eq_of_ap_empty



def RangeAt (E AP: Type _) [Fintype AP] [EvalLike E AP] : Set (Eval AP) := Set.range (@EvalLike.coe E AP _ _)

theorem rangeAt_finite : (RangeAt E AP).Finite := Eval.subset_finite

theorem rangeAt_eq_empty_of_carrier_empty [IsEmpty E] : (RangeAt E AP) = ∅ := by
  dsimp [RangeAt]
  rw [Set.range_eq_empty_iff]
  exact inferInstance

theorem rangeAt_eq_empty_iff_carrier_empty : ((RangeAt E AP) = ∅) ↔ (IsEmpty E) := by
  constructor
  · intro lm1
    dsimp [RangeAt] at lm1
    exact Set.range_eq_empty_iff.mp lm1
  · exact @rangeAt_eq_empty_of_carrier_empty E AP _ _


theorem rangeAt_eq_singleton_of_carrier_nonempty_and_ap_empty [Nonempty E] [IsEmpty AP]
  : (RangeAt E AP) = {(default: Eval AP)} := by
  dsimp [RangeAt, Inhabited.default, Indicator.equivToEval]
  simp only [Set.range_eq_singleton_iff]
  intro c
  exact Eval.all_eq_of_ap_empty


theorem rangeAt_empty_or_singleton_of_ap_empty [IsEmpty AP]
  : ((RangeAt E AP) = ∅) ∨ ((RangeAt E AP) = {(default: Eval AP)}) := by
  have lm1 := isEmpty_or_nonempty E
  rcases lm1 with lm1 | lm1
  · have lm2 := rangeAt_eq_empty_iff_carrier_empty.mpr lm1
    exact Or.inl lm2
  · have lm2 := @rangeAt_eq_singleton_of_carrier_nonempty_and_ap_empty E AP _ _ _ _
    exact Or.inr lm2





variable [DecidableEq AP]

/-
scoped instance (A: Finset AP) (a: AP) : Decidable (a ∈ A) := A.decidableMem a

def ofSubset (A: Finset AP) : Eval AP := ⟨fun a => decide (a ∈ A)⟩

theorem ofSubset_injective : Function.Injective (@ofSubset AP _ _) := by
  intro a1 a2
  unfold ofSubset
  simp
  intro lm1
  rewrite [funext_iff] at lm1
  ext a
  specialize lm1 a
  simpa only [decide_eq_decide] using lm1

theorem ofSubset_surjective : Function.Surjective (@ofSubset AP _ _) := by
  rintro ⟨a⟩
  dsimp [ofSubset]
  let a1 : Finset AP := Finset.univ.filter (a · = .true)
  exists a1
  subst a1
  refine congrArg _ ?_
  refine funext ?_; intro ap
  simp
-/

open Indicator in
instance : EvalLike (Finset AP) AP where
  coe := Eval.mk ∘ Indicator.fn ∘ equivToFinset.symm
  coe_injective := by intro _ _; simp [Indicator.fn]


instance : EvalLike (AP → Bool) AP where
  coe := Eval.mk
  coe_injective := by intro _ _; simp
  --coe_surjective := by rintro ⟨a⟩; exists a

instance (priority := 10) : EvalLike (Eval AP) AP where
  coe := id
  coe_injective := Function.injective_id

omit [DecidableEq AP] in
@[reducible]
def ofKerLift (toInd: E → AP → Bool) : EvalLike (Quotient (Setoid.ker toInd)) AP where
  coe qe := Setoid.kerLift toInd qe |> Eval.mk
  coe_injective := by
    have lm1 := @Setoid.kerLift_injective _ _ toInd
    intro _ _
    simp
    exact lm1.eq_iff.mp

end EvalLike



/-
structure SatRelRaw (AP: Type _) [Fintype AP] where
  ofRel :: rel : Eval AP → Formula AP → Prop

instance : FunLike (SatRelRaw AP) (Eval AP) (Formula AP → Prop) where
  coe x := x.rel
  coe_injective x1 x2 := by cases x1; cases x2; simp

@[mk_iff]
structure IsSatRel (AP: Type _) [Fintype AP] (raw: SatRelRaw AP) : Prop where
  true : ∀μ, raw μ (.true AP)
  atom (a: AP) : ∀μ, raw μ (.atom a) ↔ (μ a = .true)
  neg (x: Formula AP) : ∀μ, raw μ (¬ₚx) ↔ (¬raw μ x)
  and (x y: Formula AP) : ∀μ, raw μ (x ∧ₚ y) ↔ (raw μ x ∧ raw μ y)

structure SatRel (AP: Type _) [Fintype AP] where
  raw: SatRelRaw AP
  valid: IsSatRel AP raw

instance : FunLike (SatRel AP) (Eval AP) (Formula AP → Prop) where
  coe x := x.raw
  coe_injective x1 x2 := by cases x1; cases x2; simp
-/

@[mk_iff]
structure IsSatRelAt (AP: Type _) [Fintype AP] (C: Type _) (eval: C → AP → Bool) (rel: C → Formula AP → Prop) : Prop where
  true (μ: C) : rel μ (.true)
  atom (μ: C) (a: AP) : rel μ (.atom a) ↔ (eval μ a = .true)
  neg (μ: C) (x: Formula AP) : rel μ (¬ₚx) ↔ (¬rel μ x)
  and (μ: C) (x y: Formula AP) : rel μ (x ∧ₚ y) ↔ (rel μ x ∧ rel μ y)

namespace IsSatRelAt

variable {AP: Type _} [Fintype AP]
         {C: Type _} {eval: C → AP → Bool} {rel: C → Formula AP → Prop}
         {C2: Type _} {eval2: C2 → AP → Bool} {rel2: C2 → Formula AP → Prop}

theorem of_carrier_empty [IsEmpty C] : IsSatRelAt AP C eval rel := by constructor <;> simp

open EvalLike Indicator in
theorem of_eq_areEvalToTrue [EvalLike C AP] (req: rel = AreEvalToTrueAt C AP) : IsSatRelAt AP C toIndicator rel := by
  simp only [funext_iff, areEvalToTrueAt_eq_areEvalToTrue, ← AreEvalToTrue.eq_true_iff] at req
  constructor
  · intro c
    specialize req c Formula.true
    dsimp [evalFormulaToBool] at req
    simpa using req
  · intro c ap
    specialize req c (Formula.atom ap)
    dsimp [evalFormulaToBool, Indicator.fn] at req
    exact req |> propext_iff.mp
  · intro c p
    have lm1 := req c p
    have lm2 := req c p.neg
    dsimp [evalFormulaToBool, Indicator.fn] at lm2
    rw [lm2, lm1]
    simp
  · intro c p1 p2
    have lm1 := req c p1
    have lm2 := req c p2
    have lm3 := req c (p1.and p2)
    dsimp [evalFormulaToBool, Indicator.fn] at lm3
    simp at lm3
    rw [lm3, lm2, lm1]

open EvalLike Indicator in
theorem to_eq_areEvalToTrue_at [EvalLike C AP] (h: IsSatRelAt AP C toIndicator rel) (c: C) (p: Formula AP) : rel c p ↔ AreEvalToTrueAt C AP c p := by
  simp only [areEvalToTrueAt_eq_areEvalToTrue, ← AreEvalToTrue.eq_true_iff]
  obtain ⟨lm1_true, lm1_atom, lm1_neg, lm1_and⟩ := id h
  rcases p with _ | ap | p | ⟨p1, p2⟩
  · simp [evalFormulaToBool]
    exact lm1_true c
  · dsimp [evalFormulaToBool, Indicator.fn]
    exact lm1_atom c ap
  · have lm2 := h.to_eq_areEvalToTrue_at c p
    simp only [areEvalToTrueAt_eq_areEvalToTrue, ← AreEvalToTrue.eq_true_iff] at lm2
    have lm3 := lm1_neg c p
    dsimp [evalFormulaToBool, Indicator.fn]
    rw [lm3, lm2]
    simp
  · have lm2_1 := h.to_eq_areEvalToTrue_at c p1
    have lm2_2 := h.to_eq_areEvalToTrue_at c p2
    simp only [areEvalToTrueAt_eq_areEvalToTrue, ← AreEvalToTrue.eq_true_iff] at lm2_1 lm2_2
    simp [evalFormulaToBool]
    rw [← lm2_1, ← lm2_2]
    have lm3 := lm1_and c p1 p2
    exact lm3

open EvalLike in
theorem to_eq_areEvalToTrue [EvalLike C AP] (h: IsSatRelAt AP C toIndicator rel) : rel = AreEvalToTrueAt C AP := by
  simp only [funext_iff, propext_iff]
  exact h.to_eq_areEvalToTrue_at

open EvalLike in
theorem eq_areEvalToTrue_iff [EvalLike C AP] : (IsSatRelAt AP C toIndicator rel) ↔ (rel = AreEvalToTrueAt C AP) :=
  ⟨to_eq_areEvalToTrue, of_eq_areEvalToTrue⟩



/-
open EvalLike Indicator in
theorem iff_iff_toEvalFormulaToBool_eq_true [EvalLike C AP]
  : (∀c p, rel c p ↔ toEvalFormulaToBool c p = .true) ↔ IsSatRelAt AP C toIndicator rel := by
  constructor
  · exact of_iff_toEvalFormulaToBool_eq_true
  · intro lm1 c p
    have lm1_1 := lm1
    dsimp [toEvalFormulaToBool]
    rcases lm1 with ⟨lm1_true, lm1_atom, lm1_neg, lm1_and⟩
    rcases p with _ | ap | p | ⟨p1, p2⟩
    · simp [evalFormulaToBool]
      exact lm1_true c
    · dsimp [evalFormulaToBool, Indicator.fn]
      exact lm1_atom c ap
    · dsimp [evalFormulaToBool, Indicator.fn]
      have lm2 := lm1_neg c p
-/



  --dsimp [EvalToFormulaSetAt] at req
  --simp [Set.ext_iff] at req

/-
theorem of_ap_empty_at [IsEmpty AP] (req1: ∀(c: C), rel c .true) : IsSatRelAt AP C eval rel := by
  constructor
  · exact req1
  · intro _; simp only [IsEmpty.forall_iff]
  · intro c p
    rcases p with _ | ap | p | ⟨p1, p2⟩
    · simp [req1]; revert c
-/

def SetOfValidFormula (_: IsSatRelAt AP C eval rel) : Set (Formula AP) := { p: Formula AP | ∃(c: C), rel c p }


/-
open EvalLike in
theorem rangeAt_eq_iff_valid_formula_eq_of_ap_empty [IsEmpty AP]
  [EvalLike C AP] [EvalLike C2 AP] (req1: IsSatRelAt AP C toIndicator rel) (req2: IsSatRelAt AP C2 toIndicator rel2)
  : (RangeAt C AP = RangeAt C2 AP) ↔ (req1.SetOfValidFormula = req2.SetOfValidFormula) := by
  have lm1 := fun ev1 => @Eval.all_eq_of_ap_empty AP _ _ ev1 (default: Eval AP)
  dsimp [SetOfValidFormula]
  unfold toIndicator at req1 req2
  simp [lm1, DFunLike.coe] at req1 req2
  rcases req1 with ⟨req1_true, req1_atom, req1_neg, req1_and⟩
  rcases req2 with ⟨req2_true, req2_atom, req2_neg, req2_and⟩
  simp at req1_atom req2_atom
  clear req1_atom req2_atom
  dsimp [RangeAt]
  simp [Set.ext_iff]
  constructor
  · intro lm2 p
    specialize lm2 (default: Eval AP)
    simp [lm1] at lm2
-/
/-
    constructor
    · rintro ⟨c, lm3⟩
      specialize lm2 (c: Eval AP)
      simp at lm2
      rcases lm2 with ⟨c2, lm2⟩
-/


/-
  constructor
  · intro lm2
    dsimp [RangeAt] at lm2
    dsimp [SetOfValidFormula]
    simp [Set.ext_iff] at lm2 ⊢
    intro p
    constructor
    · rintro ⟨c, lm3⟩
      specialize lm2 (c: Eval AP)
      simp at lm2
      rcases lm2 with ⟨c2, lm2⟩
-/

/-
open EvalLike in
theorem rangeAt_eq_iff_valid_formula_eq
  [EvalLike C AP] [EvalLike C2 AP] (req1: IsSatRelAt AP C toIndicator rel) (req2: IsSatRelAt AP C2 toIndicator rel2)
  : (RangeAt C AP = RangeAt C2 AP) ↔ (req1.SetOfValidFormula = req2.SetOfValidFormula) := by
  --unfold toIndicator at req1 req2
  constructor
  · intro lm1
    dsimp [RangeAt] at lm1
    dsimp [SetOfValidFormula]
    simp [Set.ext_iff] at lm1 ⊢
    intro p
    constructor
    · rintro ⟨c, lm2⟩
      specialize lm1 (c: Eval AP)
      simp at lm1
      rcases lm1 with ⟨c2, lm3⟩
      exists c2
      unfold toIndicator at req1 req2
      rcases req1 with ⟨req1_true, req1_atom, req1_neg, req1_and⟩
      replace req1_true := req1_true c
      replace req1_atom := fun a => req1_atom a c
      replace req1_neg := fun a => req1_neg a c
      replace req1_and := fun a1 a2 => req1_and a1 a2 c
      rcases req2 with ⟨req2_true, req2_atom, req2_neg, req2_and⟩
      replace req2_true := req2_true c2
      replace req2_atom := fun a => req2_atom a c2
      replace req2_neg := fun a => req2_neg a c2
      replace req2_and := fun a1 a2 => req2_and a1 a2 c2
      have lm4 := isEmpty_or_nonempty AP
      rcases lm4 with lm4 | lm4
      · simp only [IsEmpty.forall_iff] at req1_atom req2_atom
        clear req1_atom req2_atom
-/
      --rcases req2 with ⟨req2_true, req2_atom, req2_neg, req2_and⟩
/-
    rcases req1 with ⟨req1_true, req1_atom, req1_neg, req1_and⟩
    rcases req2 with ⟨req2_true, req2_atom, req2_neg, req2_and⟩
    constructor
    · rintro ⟨c, lm2⟩
      specialize req1_true c
      specialize req1_neg p c
      specialize lm1 c
      simp at lm1
-/


end IsSatRelAt



abbrev IsSatRel {E AP: Type _} [Fintype AP] [EvalLike E AP] (rel: E → Formula AP → Prop) : Prop := IsSatRelAt AP E EvalLike.toIndicator rel


structure SatRel (E AP: Type _) [Fintype AP] [EvalLike E AP] where
  rel : E → Formula AP → Prop
  valid: IsSatRel rel


namespace SatRel

open EvalLike

variable {E AP: Type _} [Fintype AP] [EvalLike E AP] (sr: SatRel E AP) (μ: E)


instance : FunLike (SatRel E AP) E (Formula AP → Prop) where
  coe sr := sr.rel
  coe_injective := by
    rintro ⟨rel1⟩ ⟨rel2⟩
    simp

theorem app_eq_raw_app
  : sr μ = sr.rel μ :=
  rfl

abbrev IsSat (p: Formula AP) : Prop := sr μ p

section Notation

syntax:25 term:26 " ⊨ₚ{" term "} " term:25 : term
syntax:25 term:26 " ⊭ₚ{" term "} " term:25 : term

macro_rules
  | `( $μ ⊨ₚ{ $sr } $φ ) => ``(SatRel.IsSat $sr $μ $φ)
  | `( $μ ⊭ₚ{ $sr } $φ ) => ``(¬($μ ⊨ₚ{ $sr } $φ))

end Notation

namespace IsSat

@[scoped grind .]
theorem true_intro
  : μ ⊨ₚ{sr} (.true) := by
  simp only [IsSat, app_eq_raw_app]
  exact sr.valid.true μ

@[scoped grind =]
theorem atom_iff (a: AP)
  : μ ⊨ₚ{sr} (.atom a) ↔ (toIndicator μ) a = .true := by
  simp only [IsSat, app_eq_raw_app]
  rw [sr.valid.atom]

@[scoped grind =]
theorem neg_iff (p: Formula AP)
  : μ ⊨ₚ{sr} (¬ₚp) ↔ μ ⊭ₚ{sr} p := by
  simp only [IsSat, app_eq_raw_app _ μ]
  rw [sr.valid.neg]

@[scoped grind =]
theorem false_iff
  : μ ⊨ₚ{sr} (.false) ↔ False := by
  simp only [Formula.false]
  grind only [= neg_iff, true_intro]

@[scoped grind =]
theorem and_iff (p1 p2: Formula AP)
  : μ ⊨ₚ{sr} (p1 ∧ₚ p2) ↔ (μ ⊨ₚ{sr} p1) ∧ (μ ⊨ₚ{sr} p2) := by
  simp only [IsSat, app_eq_raw_app _ μ]
  rw [sr.valid.and]

@[scoped grind =]
theorem or_iff (p1 p2: Formula AP)
  : μ ⊨ₚ{sr} (p1 ∨ₚ p2) ↔ (μ ⊨ₚ{sr} p1) ∨ (μ ⊨ₚ{sr} p2) := by
  simp only [Formula.or]
  grind

theorem imp_iff_or (p1 p2: Formula AP)
  : μ ⊨ₚ{sr} (p1 →ₚ p2) ↔ (μ ⊭ₚ{sr} p1) ∨ (μ ⊨ₚ{sr} p2) := by
  simp only [Formula.imp]
  grind

@[scoped grind =]
theorem imp_iff_imp (p1 p2: Formula AP)
  : μ ⊨ₚ{sr} (p1 →ₚ p2) ↔ ((μ ⊨ₚ{sr} p1) → (μ ⊨ₚ{sr} p2)) := by
  simp only [imp_iff_or]
  grind only

end IsSat





/-- `p1` `p2` are semantically equivalent -/
def SemEquiv (p1 p2: Formula AP) : Prop := ∀(μ: E), (μ ⊨ₚ{sr} p1) ↔ (μ ⊨ₚ{sr} p2)


section Notation

syntax:23 term:24 " ≡ₚ{" term "} " term:23 : term

macro_rules
  | `($p1 ≡ₚ{$sr} $p2) => ``(SemEquiv $sr $p1 $p2)

end Notation

@[scoped grind =]
theorem semEquiv_iff (p1 p2: Formula AP) : sr.SemEquiv p1 p2 ↔ (∀(μ: E), (μ ⊨ₚ{sr} p1) ↔ (μ ⊨ₚ{sr} p2)) := by rfl

namespace SemEquiv

@[scoped grind ., refl]
theorem refl (p: Formula AP) : (p ≡ₚ{sr} p) := by
  unfold SemEquiv
  intro _; rfl

@[scoped grind →, symm]
theorem symm (p1 p2: Formula AP) (h: (p1 ≡ₚ{sr} p2)) : p2 ≡ₚ{sr} p1 := by
  revert h
  unfold SemEquiv
  intro h μ
  symm
  exact h μ

@[scoped grind →]
theorem trans (p1 p2 p3: Formula AP)
  (h1: (p1 ≡ₚ{sr} p2)) (h2: (p2 ≡ₚ{sr} p3))
  : p1 ≡ₚ{sr} p3 := by
  revert h1 h2
  unfold SemEquiv
  intro h1 h2 μ
  specialize h1 μ
  specialize h2 μ
  exact Iff.trans h1 h2

theorem eqv : Equivalence (· ≡ₚ{sr} ·) where
  refl := SemEquiv.refl sr
  symm := SemEquiv.symm sr _ _
  trans := SemEquiv.trans sr _ _ _

instance : IsEquiv (Formula AP) (· ≡ₚ{sr} ·) := IsEquiv.of_equivalence (SemEquiv.eqv sr)



@[reducible]
def toSetoid : Setoid (Formula AP) where
  r := sr.SemEquiv
  iseqv := SemEquiv.eqv sr


open scoped IsSat

@[scoped grind .]
theorem neg_neg (p: Formula AP)
  : ¬ₚ¬ₚp ≡ₚ{sr} p := by
  grind only [= semEquiv_iff, → symm, = IsSat.neg_iff]

@[scoped grind .]
theorem id_or (p: Formula AP)
  : p ∨ₚ p ≡ₚ{sr} p := by
  grind only [= semEquiv_iff, → symm, = IsSat.or_iff]

@[scoped grind .]
theorem id_and (p: Formula AP)
  : p ∧ₚ p ≡ₚ{sr} p := by
  grind only [= semEquiv_iff, → symm, = IsSat.and_iff]

@[scoped grind .]
theorem absorb_and (p1 p2: Formula AP)
  : p1 ∧ₚ (p2 ∨ₚ p1) ≡ₚ{sr} p1 := by
  grind only [= semEquiv_iff, → symm, = IsSat.and_iff, = IsSat.or_iff]

@[scoped grind .]
theorem absorb_or (p1 p2: Formula AP)
  : p1 ∨ₚ (p2 ∧ₚ p1) ≡ₚ{sr} p1 := by
  grind only [= semEquiv_iff, → symm, = IsSat.or_iff, = IsSat.and_iff]

@[scoped grind .]
theorem comm_or (p1 p2: Formula AP)
  : p1 ∨ₚ p2 ≡ₚ{sr} p2 ∨ₚ p1 := by
  grind only [= semEquiv_iff, → symm, = IsSat.or_iff]

@[scoped grind .]
theorem comm_and (p1 p2: Formula AP)
  : p1 ∧ₚ p2 ≡ₚ{sr} p2 ∧ₚ p1 := by
  grind only [= semEquiv_iff, → symm, = IsSat.and_iff]

@[scoped grind .]
theorem assoc_and (p1 p2 p3: Formula AP)
  : p1 ∧ₚ (p2 ∧ₚ p3) ≡ₚ{sr} (p1 ∧ₚ p2) ∧ₚ p3 := by
  grind only [= semEquiv_iff, → symm, = IsSat.and_iff]

@[scoped grind .]
theorem assoc_or (p1 p2 p3: Formula AP)
  : p1 ∨ₚ (p2 ∨ₚ p3) ≡ₚ{sr} (p1 ∨ₚ p2) ∨ₚ p3 := by
  grind only [= semEquiv_iff, → symm, = IsSat.or_iff]

@[scoped grind .]
theorem demorgan_and (p1 p2: Formula AP)
  : ¬ₚ(p1 ∧ₚ p2) ≡ₚ{sr} (¬ₚp1 ∨ₚ ¬ₚp2) := by
  grind only [= semEquiv_iff, → symm, = IsSat.neg_iff, = IsSat.or_iff, = IsSat.and_iff]

@[scoped grind .]
theorem demorgan_or (p1 p2: Formula AP)
  : ¬ₚ(p1 ∨ₚ p2) ≡ₚ{sr} (¬ₚp1 ∧ₚ ¬ₚp2) := by
  grind only [= semEquiv_iff, → symm, = IsSat.neg_iff, = IsSat.and_iff, = IsSat.or_iff]

@[scoped grind .]
theorem dist_or (p1 p2 p3: Formula AP)
  : p1 ∨ₚ (p2 ∧ₚ p3) ≡ₚ{sr} (p1 ∨ₚ p2) ∧ₚ (p1 ∨ₚ p3) := by
  grind

@[scoped grind .]
theorem dist_and (p1 p2 p3: Formula AP)
  : p1 ∧ₚ (p2 ∨ₚ p3) ≡ₚ{sr} (p1 ∧ₚ p2) ∨ₚ (p1 ∧ₚ p3) := by
  grind

@[scoped grind =]
theorem iterAnd_nil : ⋀ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.true) := by
  unfold Formula.iterAnd
  rfl

@[scoped grind .]
theorem iterAnd_cons (p: Formula AP) (ps: List (Formula AP))
  : ⋀ₚ (p :: ps) ≡ₚ{sr} (p ∧ₚ (⋀ₚ ps)) := by
  dsimp [Formula.iterAnd]
  rfl

@[scoped grind =]
theorem iterOr_nil : ⋁ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.false) := by
  unfold Formula.iterOr
  rfl

@[scoped grind .]
theorem iterOr_cons (p: Formula AP) (ps: List (Formula AP))
  : ⋁ₚ (p :: ps) ≡ₚ{sr} (p ∨ₚ (⋁ₚ ps)) := by
  dsimp [Formula.iterOr]
  rfl

end SemEquiv

def IsSatisfiable (p: Formula AP) : Prop := ∃(μ: E), μ ⊨ₚ{sr} p

def IsValid (p: Formula AP) : Prop := ∀(μ: E), μ ⊨ₚ{sr} p

abbrev IsUnsatisfiable (p: Formula AP) : Prop := ¬(sr.IsSatisfiable p)

theorem unsatisfiable_iff_neg_valid (p: Formula AP)
  : sr.IsUnsatisfiable p ↔ sr.IsValid (¬ₚp) := by
  simp only [IsUnsatisfiable, IsSatisfiable, IsValid]
  simp only [not_exists]
  simp only [IsSat.neg_iff]


protected def default : SatRel E AP where
  rel := AreEvalToTrueAt E AP
  valid := IsSatRelAt.of_eq_areEvalToTrue rfl


instance toUnique : Unique (SatRel E AP) where
  default := SatRel.default
  uniq := by
    rintro ⟨rel, valid⟩
    dsimp [SatRel.default]
    simp
    dsimp [IsSatRel] at valid
    exact valid.to_eq_areEvalToTrue


def defaultAt (E AP: Type _) [Fintype AP] [EvalLike E AP] : SatRel E AP :=
  (inferInstance: Unique (SatRel E AP)).toInhabited.default

section Notation

syntax:25 term:26 " ⊨ₚ " term:25 : term

macro_rules
  | `($μ ⊨ₚ $φ) => ``($μ ⊨ₚ{ defaultAt _ _ } $φ )


syntax:25 term:26 " ⊨ₚ{ " term ", " term ", " term ", " term " }" term:25 : term

macro_rules
  | `($μ ⊨ₚ{ $EC , $AP , $ft , $el } $φ) => ``( @IsSat $EC $AP $ft $el (@defaultAt $EC $AP $ft $el) $μ $φ )


syntax:25 term:26 " ⊨ₚ⟦ " term " ⟧ "  term:25 : term

macro_rules
  | `($μ ⊨ₚ⟦ $toInd ⟧ $φ) => ``( $μ ⊨ₚ{ _, _, _, EvalLike.ofKerLift $toInd } $φ )

end Notation


namespace IsSat

open scoped SemEquiv

theorem iterAnd_nil : μ ⊨ₚ{sr} ⋀ₚ ([]: List (Formula AP)) := by
  grind


theorem iterAnd_cons (p: Formula AP) (ps: List (Formula AP))
  : (μ ⊨ₚ{sr} ⋀ₚ (p :: ps)) ↔ (μ ⊨ₚ{sr} (p ∧ₚ (⋀ₚ ps))) := by
  have lm1 := SemEquiv.iterAnd_cons sr p ps
  grind


theorem iterOr_nil : ⋁ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.false) := by
  unfold Formula.iterOr
  rfl


theorem iterOr_cons (p: Formula AP) (ps: List (Formula AP))
  : ⋁ₚ (p :: ps) ≡ₚ{sr} (p ∨ₚ (⋁ₚ ps)) := by
  dsimp [Formula.iterOr]
  rfl

end IsSat


end SatRel


end Nemonuri.PropositionalLogics

end
