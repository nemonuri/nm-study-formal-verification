module


public meta import Nemonuri.PropositionalLogics.Attributes
public import Mathlib.Data.Fintype.Basic


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], A.3 Propositional Logic, p.915

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics


inductive Formula (AP: Type _) where
  | true
  | atom (x: AP)
  | neg (x: Formula AP)
  | and (x: Formula AP) (y: Formula AP)


namespace Formula

variable {AP: Type _} --[Fintype AP]

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

@[pl_simp]
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

@[defeq, pl_simp]
theorem iterAnd_nil : (⋀ₚ ([]: List (Formula AP))) = .true := rfl

@[defeq, pl_simp]
theorem iterAnd_cons {x: Formula AP} {xs: List (Formula AP)} : (⋀ₚ (x :: xs)) = (x ∧ₚ (⋀ₚ xs)) := rfl

@[defeq, pl_simp]
theorem atomTuple_nil : atomTuple ([]: List AP) = .true := by
  dsimp [atomTuple, iterAnd_nil]

@[defeq, pl_simp]
theorem atomTuple_cons {a: AP} {as: List AP} : atomTuple (a::as) = ((.atom a) ∧ₚ (.atomTuple as)) := by
  dsimp [atomTuple, iterAnd_cons]


section DecidableEqSection

variable [DecidableEq AP]

def areSyntaxEq : Formula AP → Formula AP → Bool
  | .true, .true => .true
  | .atom ap1, .atom ap2 => decide (ap1 = ap2)
  | .neg fml1, .neg fml2 => areSyntaxEq fml1 fml2
  | .and fmlL1 fmlR1, .and fmlL2 fmlR2 => (areSyntaxEq fmlL1 fmlL2) && (areSyntaxEq fmlR1 fmlR2)
  | _, _ => .false

theorem areSyntaxEq_eq_true_iff_eq {AP: Type*} [DecidableEq AP] {fml1 fml2: Formula AP}
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

end DecidableEqSection






end Formula


end Nemonuri.PropositionalLogics

end
