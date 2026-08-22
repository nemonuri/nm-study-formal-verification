module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finite.Prod

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

end Formula


structure Eval (AP: Type _) [Fintype AP] where
  eval : AP → Bool

namespace Eval

variable {AP: Type _} [Fintype AP]

instance : FunLike (Eval AP) AP Bool where
  coe μ := μ.eval
  coe_injective μ1 μ2 := by cases μ1; cases μ2; simp

theorem app_eq_eval_app (μ: Eval AP) (a: AP) : μ a = μ.eval a := by rfl

abbrev Indicator (AP: Type _) [Fintype AP] : Type _ := AP → Bool

@[defeq]
theorem indicator_def : Indicator AP = (AP → Bool) := rfl

namespace Indicator

def mk (f: AP → Bool) : Indicator AP := f

def fn (ind: Indicator AP) : AP → Bool := ind


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


end Indicator


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

def toIndicator (e: E) : Eval.Indicator AP := ((e: Eval AP) : AP → Bool)



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
  dsimp [RangeAt, Inhabited.default, Eval.Indicator.equivToEval]
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


instance : EvalLike (Finset AP) AP where
  coe := ofSubset
  coe_injective := ofSubset_injective
  --coe_surjective := ofSubset_surjective

instance : EvalLike (AP → Bool) AP where
  coe := Eval.mk
  coe_injective := by intro _ _; simp
  --coe_surjective := by rintro ⟨a⟩; exists a



end EvalLike

namespace Formula

class HasEvalLike (AP: Type*) [Fintype AP] where
  Carrier: Type*
  [evalLike: EvalLike Carrier AP]

attribute [reducible] HasEvalLike.Carrier
attribute [reducible, instance] HasEvalLike.evalLike

end Formula

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
  true : ∀μ, rel μ (.true)
  atom (a: AP) : ∀μ, rel μ (.atom a) ↔ (eval μ a = .true)
  neg (x: Formula AP) : ∀μ, rel μ (¬ₚx) ↔ (¬rel μ x)
  and (x y: Formula AP) : ∀μ, rel μ (x ∧ₚ y) ↔ (rel μ x ∧ rel μ y)

namespace IsSatRelAt

variable {AP: Type _} [Fintype AP]
         {C: Type _} {eval: C → AP → Bool} {rel: C → Formula AP → Prop}
         {C2: Type _} {eval2: C2 → AP → Bool} {rel2: C2 → Formula AP → Prop}

def SetOfValidFormula (_: IsSatRelAt AP C eval rel) : Set (Formula AP) := { p: Formula AP | ∃(c: C), rel c p }

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

namespace Eval

abbrev IsSatRel {AP: Type _} [Fintype AP] (rel: Eval AP → Formula AP → Prop) : Prop := IsSatRelAt AP (Eval AP) DFunLike.coe rel


structure SatRel (AP: Type _) [Fintype AP] where
  rel : Eval AP → Formula AP → Prop
  valid: IsSatRel rel

instance {AP: Type _} [Fintype AP] : FunLike (SatRel AP) (Eval AP) (Formula AP → Prop) where
  coe sr := sr.rel
  coe_injective := by
    rintro ⟨rel1⟩ ⟨rel2⟩
    simp


namespace SatRel


variable {AP: Type _} [Fintype AP] (sr: SatRel AP) (μ: Eval AP)


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
  : μ ⊨ₚ{sr} (.atom a) ↔ μ a = .true := by
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
def SemEquiv (p1 p2: Formula AP) : Prop := ∀(μ: Eval AP), (μ ⊨ₚ{sr} p1) ↔ (μ ⊨ₚ{sr} p2)


section Notation

syntax:23 term:24 " ≡ₚ{" term "} " term:23 : term

macro_rules
  | `($p1 ≡ₚ{$sr} $p2) => ``(SemEquiv $sr $p1 $p2)

end Notation

@[scoped grind =]
theorem semEquiv_iff (p1 p2: Formula AP) : sr.SemEquiv p1 p2 ↔ (∀(μ: Eval AP), (μ ⊨ₚ{sr} p1) ↔ (μ ⊨ₚ{sr} p2)) := by rfl

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

@[scoped grind .]
theorem iterAnd_nil : ⋀ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.true) := by
  unfold Formula.iterAnd
  rfl

@[scoped grind .]
theorem iterOr_nil : ⋁ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.false) := by
  unfold Formula.iterOr
  rfl

end SemEquiv

def IsSatisfiable (p: Formula AP) : Prop := ∃(μ: Eval AP), μ ⊨ₚ{sr} p

def IsValid (p: Formula AP) : Prop := ∀(μ: Eval AP), μ ⊨ₚ{sr} p

abbrev IsUnsatisfiable (p: Formula AP) : Prop := ¬(sr.IsSatisfiable p)

theorem unsatisfiable_iff_neg_valid (p: Formula AP)
  : sr.IsUnsatisfiable p ↔ sr.IsValid (¬ₚp) := by
  simp only [IsUnsatisfiable, IsSatisfiable, IsValid]
  simp only [not_exists]
  simp only [IsSat.neg_iff]


end SatRel

end Eval

namespace EvalLike

variable {E: Type _} {AP: Type _} [Fintype AP] [EvalLike E AP]

def toBoolPred (e: E) : AP → Bool := (e: Eval AP)

abbrev IsSatRel (rel: E → Formula AP → Prop) : Prop := IsSatRelAt AP E toBoolPred rel


class HasSatRel (E: Type _) (AP: Type _) [Fintype AP] [EvalLike E AP] where
  rel : E → Formula AP → Prop
  valid : IsSatRel rel

namespace HasSatRel


def liftToEvalAt (E: Type _) (AP: Type _) [Fintype AP] [EvalLike E AP] [HasSatRel E AP] : Eval.SatRel AP where
  rel ev p := (∃(e: E), ((e: Eval AP) = ev) ∧ (HasSatRel.rel e p)) /-(∀(e: E), ((e: Eval AP) ≠ ev)) ∨ -/
  valid := by
    have lm1 := @HasSatRel.valid E AP _ _ _
    rcases lm1 with ⟨lm1_true, lm1_atom, lm1_neg, lm1_and⟩
    have lm2 := @EvalLike.coe_injective E AP _ _
    have lm3 := @EvalLike.coe_surjective E AP _ _
    constructor
    · intro ev
      by_contra lm4
      simp at lm4
      obtain ⟨e, lm5⟩ := @lm3 ev
      specialize lm4 e lm5
      specialize lm1_true e
      exact lm4 lm1_true
    · intro a ev
      obtain ⟨e, lm4⟩ := @lm3 ev
      dsimp [toBoolPred] at lm1_atom
      specialize lm1_atom a e
      rewrite [lm4] at lm1_atom
      rw [← lm1_atom]
      constructor
      · rintro ⟨e2, lm5, lm6⟩
        replace lm5 := Eq.trans lm4 lm5.symm |> lm2.eq_iff.mp
        rw [lm5]
        exact lm6
      · intro lm5
        exists e
    · intro p ev
      obtain ⟨e, lm4⟩ := @lm3 ev
      specialize lm1_neg p e
      constructor
      · simp
        intro e2 lm5 lm6 e3 lm7
        replace lm5 := Eq.trans lm4 lm5.symm |> lm2.eq_iff.mp
        subst lm5
        replace lm7 := Eq.trans lm4 lm7.symm |> lm2.eq_iff.mp
        subst lm7
        exact lm1_neg.mp lm6
      · simp
        intro lm5
        specialize lm5 e lm4
        exists e
        simp [lm4]
        exact lm1_neg.mpr lm5
    · intro p1 p2 ev
      specialize lm1_and p1 p2
      constructor
      · simp
        intro e lm4 lm5
        by_contra lm6
        simp at lm6
        specialize lm6 e lm4
        specialize lm1_and e
        obtain ⟨lm1_and_1, lm1_and_2⟩ := lm1_and.mp lm5; clear lm1_and
        exact lm6 lm1_and_1 e lm4 lm1_and_2
      · simp
        intro e lm4 lm5 e2 lm6 lm7
        exists e
        simp [lm4]
        rw [lm1_and e]
        replace lm6 := Eq.trans lm4 lm6.symm |> lm2.eq_iff.mp
        subst lm6
        exact And.intro lm5 lm7

open Formula in
abbrev liftToEval (AP: Type _) [Fintype AP] [HasEvalLike AP] [HasSatRel (HasEvalLike.Carrier AP) AP] : Eval.SatRel AP := liftToEvalAt (HasEvalLike.Carrier AP) AP

section Notation

syntax:25 term:26 " ⊨ₚ " term:25 : term

macro_rules
  | `($μ ⊨ₚ $φ) => ``($μ ⊨ₚ{ HasSatRel.liftToEval _ } $φ )

end Notation

/-
      rcases lm3 with ⟨⟨e, lm3⟩, lm4⟩
      specialize lm4 e lm3
      specialize lm1_true e
      exact lm4 lm1_true
    · intro ap ev
      specialize lm1_atom ap
      dsimp [toBoolPred] at lm1_atom
      constructor
      · intro lm3
        rcases lm3 with lm3 | lm3
        · have := lm2.left
-/
/-
    have lm1 := @HasSatRel.valid E AP _ _ _
    rcases lm1 with ⟨lm1_true, lm1_atom, lm1_neg, lm1_and⟩
    have lm2 := @EvalLike.coe_injective E AP _ _
    constructor
    · intro ev
      by_contra lm3
      simp at lm3
      rcases lm3 with ⟨lm3, lm4⟩
      rcases lm3 with ⟨e⟩
      specialize lm4 e
-/

/-
  ∃(prop: Prop), (Option.some prop = (do let e: E ← Function.partialInv (EvalLike.coe) ev; return HasSatRel.rel e p)) ∧ prop
-/
/-
  valid := by
    have lm1 := @EvalLike.coe_injective E AP _ _
    have lm2 := Function.partialInv_left lm1
    simp
    dsimp [Eval.IsSatRel, DFunLike.coe]
    constructor
    · intro ev
-/
    --simp [Option.bind_eq_some_iff]


end HasSatRel

end EvalLike

/-
class HasSatRelAt {AP: Type _} [Fintype AP] (μ: Eval AP) (p: Formula AP) where
  satRel: SatRel AP


section Notation

syntax:25 term:26 " ⊨ₚ " term:25 : term

macro_rules
  | `($μ ⊨ₚ $φ) => ``($μ ⊨ₚ{ HasSatRelAt.satRel $μ $φ } $φ )

end Notation


namespace HasSatRelAt

variable {E AP: Type _} [Fintype AP] [EvalLike E AP]
-/


/-
instance ofEvalLike (e: E) (p: Formula AP) : HasSatRelAt (e: Eval AP) p where
  satRel := {
    rel :=
    valid := _
  }
-/




/-
class SatRelLike (SR: Type _) (E: Type _) (AP: outParam <| Type _) [Fintype AP] [EvalLike E AP] where
  toRel : SR → E → Formula AP → Prop
  valid (sr: SR) : IsSatRel AP (fun ev => toRel sr (EvalLike.coeInv ev))
-/
/-
  true (sr: SR) : ∀μ, toRel sr μ (.true)
  atom (sr: SR) (a: AP) : ∀μ, toRel sr μ (.atom a) ↔ ((μ: Eval AP) a = .true)
  neg (sr: SR) (x: Formula AP) : ∀μ, toRel sr μ (¬ₚx) ↔ (¬toRel sr μ x)
  and (sr: SR) (x y: Formula AP) : ∀μ, toRel sr μ (x ∧ₚ y) ↔ (toRel sr μ x ∧ toRel sr μ y)
-/

/-
namespace SatRelLike

variable {SR E AP: Type _} [Fintype AP] [EvalLike E AP] [SatRelLike SR E AP]


def toSatRel (sr: SR) : SatRel AP where
  rel ev := toRel sr (EvalLike.coeInv ev : E)
  valid := SatRelLike.valid sr

#print toSatRel


end SatRelLike
-/

end Nemonuri.PropositionalLogics

end
