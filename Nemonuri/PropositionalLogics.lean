module

public import Nemonuri.FinsetLike

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], A.3 Propositional Logic, p.915

-/

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

protected def eqv (x y: Formula AP) : Formula AP := .or (.and (.neg x) (.neg y)) (.and x y)

protected def false (AP: Finset Atom) : Formula AP := .neg (.true AP)

def iterAnd (xs: List (Formula AP)) : Formula AP :=
  match xs with
  | [] => (.true AP)
  | hd::tl => .and hd (iterAnd tl)

def iterOr (xs: List (Formula AP)) : Formula AP :=
  match xs with
  | [] => (.false AP)
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



structure Eval (AP: Finset Atom) where
  eval : AP → Bool

namespace Eval

instance : FunLike (Eval AP) AP Bool where
  coe μ := μ.eval
  coe_injective μ1 μ2 := by cases μ1; cases μ2; simp

theorem app_eq_eval_app (μ: Eval AP) (a: AP) : μ a = μ.eval a := by rfl



instance : FinsetLike (Eval AP) AP where
  coe := (FinsetLike.coeBoolPredFor AP) ∘ (Eval.eval ·)
  coe_injective := (FinsetLike.coeBoolPredFor_injective AP).comp (by rintro ⟨ev1⟩ ⟨ev2⟩; simp)



section Coe

class EvalLike (E: Type _) {Atom: outParam <| Type _} (AP: outParam <| Finset Atom) where
  protected coe (e: E) : Eval AP
  coe_injective : Function.Injective coe

namespace EvalLike

attribute [coe] EvalLike.coe

variable {E: Type _} {Atom: Type _} {AP: Finset Atom} [EvalLike E AP]

instance : CoeOut E (Eval AP) where coe := EvalLike.coe

end EvalLike


variable [DecidableEq AP]

scoped instance (A: Finset AP) (a: AP) : Decidable (a ∈ A) := A.decidableMem a

def ofSubset (A: Finset AP) : Eval AP := ⟨fun a => decide (a ∈ A)⟩

theorem ofSubset_injective : Function.Injective (@ofSubset _ AP _) := by
  intro a1 a2
  unfold ofSubset
  simp
  intro lm1
  rewrite [funext_iff] at lm1
  ext a
  specialize lm1 a
  simpa only [decide_eq_decide] using lm1


instance : EvalLike (Finset AP) AP where
  coe := ofSubset
  coe_injective := ofSubset_injective

instance : EvalLike (AP → Bool) AP where
  coe := Eval.mk
  coe_injective := by intro _ _; simp

instance [ft: Fintype Atom] [DecidableEq Atom] : EvalLike (Finset Atom) (ft: Finset Atom) :=
  let attachUniv : Function.Embedding Atom (.univ: Finset Atom) :=
    .mk (fun x => ⟨x, Finset.mem_univ x⟩) (by intro _ _; simp)
  { coe := fun (fs: Finset Atom) => fs.map attachUniv
    coe_injective fs1 fs2 := by
      subst attachUniv
      intro lm1
      simpa [EvalLike.coe_injective.eq_iff] using lm1 }

instance [ft: Fintype Atom] : EvalLike (Atom → Bool) (ft: Finset Atom) where
  coe f := fun (a: (ft: Finset Atom)) => f a
  coe_injective f1 f2 := by
    simp only
    intro lm1
    simp only [EvalLike.coe_injective.eq_iff] at lm1
    simp [funext_iff] at lm1
    ext a
    exact lm1 a (Finset.mem_univ a)



end Coe

end Eval


structure SatRelRaw (AP: Finset Atom) where
  ofRel :: rel : Eval AP → Formula AP → Prop

instance : FunLike (SatRelRaw AP) (Eval AP) (Formula AP → Prop) where
  coe x := x.rel
  coe_injective x1 x2 := by cases x1; cases x2; simp

@[mk_iff]
structure IsSatRel (AP: Finset Atom) (raw: SatRelRaw AP) : Prop where
  true : ∀μ, raw μ (.true AP)
  atom (a: AP) : ∀μ, raw μ (.atom AP a) ↔ (μ a = .true)
  neg (x: Formula AP) : ∀μ, raw μ (¬ₚx) ↔ (¬raw μ x)
  and (x y: Formula AP) : ∀μ, raw μ (x ∧ₚ y) ↔ (raw μ x ∧ raw μ y)

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
  : μ ⊨ₚ{sr} (.true AP) := by
  simp only [IsSat, app_eq_raw_app]
  exact sr.is_sat_rel.true μ

@[scoped grind =]
theorem atom_iff (a: AP)
  : μ ⊨ₚ{sr} (.atom AP a) ↔ μ a = .true := by
  simp only [IsSat, app_eq_raw_app]
  rw [sr.is_sat_rel.atom]

@[scoped grind =]
theorem neg_iff (p: Formula AP)
  : μ ⊨ₚ{sr} (¬ₚp) ↔ μ ⊭ₚ{sr} p := by
  simp only [IsSat, app_eq_raw_app _ μ]
  rw [sr.is_sat_rel.neg]

@[scoped grind =]
theorem false_iff
  : μ ⊨ₚ{sr} (.false AP) ↔ False := by
  simp only [Formula.false]
  grind only [= neg_iff, true_intro]

@[scoped grind =]
theorem and_iff (p1 p2: Formula AP)
  : μ ⊨ₚ{sr} (p1 ∧ₚ p2) ↔ (μ ⊨ₚ{sr} p1) ∧ (μ ⊨ₚ{sr} p2) := by
  simp only [IsSat, app_eq_raw_app _ μ]
  rw [sr.is_sat_rel.and]

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



class HasSatRelAt (AP: Finset Atom) (μ: Eval AP) (p: Formula AP) where
  satRel: SatRel AP

abbrev HasSatRel (Atom: Type _) : Type _ := (AP: Finset Atom) → (μ: Eval AP) → (p: Formula AP) → HasSatRelAt AP μ p


section Notation

syntax:25 term:26 " ⊨ₚ " term:25 : term

macro_rules
  | `($μ ⊨ₚ $φ) => ``($μ ⊨ₚ{ HasSatRelAt.satRel $μ $φ } $φ )

end Notation


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
theorem iterAnd_nil : ⋀ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.true AP) := by
  unfold iterAnd
  rfl

@[scoped grind .]
theorem iterOr_nil : ⋁ₚ ([]: List (Formula AP)) ≡ₚ{sr} (.false AP) := by
  unfold iterOr
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










end Formula






end Nemonuri.PropositionalLogics

end
