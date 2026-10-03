module

--public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Defs
--public meta import Mathlib.Tactic.TypeStar

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

inductive Label where
  | fst
  | snd
  deriving DecidableEq

namespace Label

instance : Nonempty Label := .intro .fst

abbrev toDual (lb: Label) : Label := lb.casesOn Label.snd Label.fst

@[defeq, simp]
theorem fst_toDual : Label.fst.toDual = .snd := rfl

@[defeq, simp]
theorem snd_toDual : Label.snd.toDual = .fst := rfl

theorem ne_iff_eq_toDual {lb1 lb2: Label} : (lb1 ≠ lb2) ↔ (lb1 = lb2.toDual) := by
  dsimp [toDual]
  rcases lb1 <;> rcases lb2 <;> simp


theorem toDual_toDual_eq_self {lb: Label} : lb.toDual.toDual = lb := by
  rcases lb <;> dsimp [toDual]

theorem eq_toDual_symm {lb1 lb2: Label} (req: lb1 = lb2.toDual) : lb2 = lb1.toDual := by
  replace req := congrArg (Label.toDual) req
  simp [toDual_toDual_eq_self] at req
  exact req.symm

theorem ne_iff_eq_toDual_symm {lb1 lb2: Label} : (lb1 ≠ lb2) ↔ (lb2 = lb1.toDual) := by
  rw [ne_iff_eq_toDual]
  constructor
  · intro lm1
    exact eq_toDual_symm lm1
  · intro lm1
    exact eq_toDual_symm lm1

theorem forall_iff_fst_and_snd {p: Label → Prop} : (∀(lb: Label), p lb) ↔ (p .fst ∧ p .snd) := by
  constructor
  · intro lm1
    exact ⟨lm1 .fst, lm1 .snd⟩
  · rintro ⟨lm1, lm2⟩ lb
    rcases lb
    · exact lm1
    · exact lm2

theorem exists_iff_fst_or_snd {p: Label → Prop} : (∃(lb: Label), p lb) ↔ (p .fst ∨ p .snd) := by
  constructor
  · rintro ⟨lb, lm1⟩
    rcases lb
    · exact Or.inl lm1
    · exact Or.inr lm1
  · intro lm1
    rcases lm1 with lm1 | lm1
    · exists .fst
    · exists .snd


@[simp]
theorem snd_eq_fst_iff_fst_eq_snd {α: Sort*} {f1 f2: Label → α} : (f2 .snd = f1 .fst) ↔ (f1 .fst = f2 .snd) := by rw [Eq.comm]

theorem snd_fst_iff_fst_snd {α: Sort*} {f1 f2: Label → α} {r: α → α → Prop} [Std.Symm r]
  : r (f2 .snd) (f1 .fst) ↔ r (f1 .fst) (f2 .snd) := by
  have lm1 : Std.Symm r := inferInstance
  constructor
  · exact lm1.symm _ _
  · exact lm1.symm _ _

theorem toDual_iff_toDual {α: Sort*} {f1 f2: Label → α} {r: α → α → Prop} [Std.Symm r] {lb: Label}
  : r (f2 lb.toDual) (f1 lb) ↔ r (f1 lb) (f2 lb.toDual) := by
  rcases lb <;> simp only [snd_fst_iff_fst_snd]



def projectProd (lb: Label) {α β: Type _} (prod: α × β) : lb.casesOn α β := lb.casesOn prod.fst prod.snd

section ProjectProd

variable {α β: Type _} {prod: α × β}

@[defeq]
theorem projectProd_prod_eq
  : (Label.fst.projectProd prod, Label.snd.projectProd prod) = prod := by
  dsimp [projectProd]

@[defeq]
theorem projectProd_prod_fst_eq
  : Label.fst.projectProd prod = prod.fst := by
  dsimp [projectProd]

@[defeq]
theorem projectProd_prod_snd_eq
  : Label.snd.projectProd prod = prod.snd := by
  dsimp [projectProd]

end ProjectProd

def MatchSort (lb: Label) (α β: Sort uh) : Sort uh := lb.casesOn α β

namespace MatchSort

@[defeq, simp]
theorem fst_eq {α β: Sort uh} : Label.fst.MatchSort α β = α := rfl

@[defeq, simp]
theorem snd_eq {α β: Sort uh} : Label.snd.MatchSort α β = β := rfl

def ofCases.{u} {lb: Label} {α β: Sort uh} (fst: α → Sort u) (snd: β → Sort u) : MatchSort lb (α → Sort u) (β → Sort u) := lb.casesOn fst snd

theorem motive_eq.{u} {lb: Label} {α β: Sort uh} : MatchSort lb (α → Sort u) (β → Sort u) = (MatchSort lb α β → Sort u) := by
  rcases lb <;> dsimp

def equivOfMotive.{u} {lb: Label} {α β: Sort uh} : MatchSort lb (α → Sort u) (β → Sort u) ≃ (MatchSort lb α β → Sort u) := Equiv.cast motive_eq

def equivOfPred {lb: Label} {α β: Sort uh} : MatchSort lb (α → Prop) (β → Prop) ≃ (MatchSort lb α β → Prop) := equivOfMotive.{uh, 0}

def mergeMotive.{uh2} (lb: Label) {α β: Sort uh} (fst: α → Sort uh2) (snd: β → Sort uh2) : MatchSort lb α β → Sort uh2 := equivOfMotive (ofCases fst snd)

@[defeq, simp]
theorem mergeMotive_fst {α β: Sort _} {fst: α → Sort _} {snd: β → Sort _} : mergeMotive .fst fst snd = fst := by
  dsimp only [mergeMotive, ofCases, equivOfMotive, Equiv.cast_apply, cast]

@[defeq, simp]
theorem mergeMotive_snd {α β: Sort _} {fst: α → Sort _} {snd: β → Sort _} : mergeMotive .snd fst snd = snd := by
  dsimp only [mergeMotive, ofCases, equivOfMotive, Equiv.cast_apply, cast]

def mergePred (lb: Label) {α β: Sort uh} (fst: α → Prop) (snd: β → Prop) : MatchSort lb α β → Prop := mergeMotive.{uh, 0} lb fst snd


theorem fun_eq.{u} {lb: Label} {α β: Sort uh} {α2 β2: Sort u} : MatchSort lb (α → α2) (β → β2) = (MatchSort lb α β → MatchSort lb α2 β2) := by
  rcases lb <;> dsimp

def equivOfFun.{uh2} {lb: Label} {α β: Sort uh} {α2 β2: Sort uh2} : MatchSort lb (α → α2) (β → β2) ≃ (MatchSort lb α β → MatchSort lb α2 β2) := Equiv.cast fun_eq


inductive Mem {α β: Sort uh} (f1: α → β) (f2: β → α) : (lb1: Label) → (lb1.MatchSort α β) → (lb2: Label) → (lb2.MatchSort α β → Prop) → Prop where
  | label_eq (lb: Label) (val: lb.MatchSort α β) (pred: lb.MatchSort α β → Prop) (req: pred val) : Mem f1 f2 lb val lb pred
  | fst_snd (val: α) (pred: β → Prop) (req: pred (f1 val)) : Mem f1 f2 .fst val .snd pred
  | snd_fst (val: β) (pred: α → Prop) (req: pred (f2 val)) : Mem f1 f2 .snd val .fst pred

def mapFun.{uh2} {α β: Sort uh} {α2 β2: Sort uh2} (f1: α → β) (f2: β → α) (f3: α2 → β2) (f4: β2 → α2)
  (lb1: Label) (f: MatchSort lb1 α β → MatchSort lb1 α2 β2)
  (lb2: Label) (x: lb2.MatchSort α β) : lb2.MatchSort α2 β2 :=
  match lb1, lb2 with
  | .fst, .fst => f x
  | .snd, .snd => f x
  | .fst, .snd => f3 (f (f2 x))
  | .snd, .fst => f4 (f (f1 x))


def pi_eq.{uh2} {lb: Label} {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2}
  : MatchSort lb ((x: α1) → β1 x) ((x: α2) → β2 x) = ((x: MatchSort lb α1 α2) → mergeMotive lb β1 β2 x) := by
  rcases lb <;> dsimp

def equivOfPi.{uh2} {lb: Label} {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2} : MatchSort lb ((x: α1) → β1 x) ((x: α2) → β2 x) ≃ ((x: MatchSort lb α1 α2) → mergeMotive lb β1 β2 x) :=
  Equiv.cast pi_eq



end MatchSort

end Label


end Nemonuri.Relations.Heterogeneous

end
