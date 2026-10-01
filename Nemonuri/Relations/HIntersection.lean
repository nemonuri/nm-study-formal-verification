module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations

universe uh

structure HIntersection (α β: Sort uh) where
  rel: α → β → Prop
  biUnique: Relator.BiUnique rel

namespace HIntersection

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

@[defeq, simp]
theorem matchSort_fst {α β: Sort uh} : Label.fst.MatchSort α β = α := rfl

@[defeq, simp]
theorem matchSort_snd {α β: Sort uh} : Label.snd.MatchSort α β = β := rfl

end Label

structure LabelSum (α β: Sort uh) where
  label: Label
  val: label.MatchSort α β

namespace LabelSum

variable {α β: Sort uh}

@[match_pattern]
def ofFst (a: α) : LabelSum α β := ⟨.fst, a⟩

@[match_pattern]
def ofSnd (b: β) : LabelSum α β := ⟨.snd, b⟩

def toPSum : LabelSum α β → PSum α β
  | .ofFst a => .inl a
  | .ofSnd b => .inr b

def ofPSum : PSum α β → LabelSum α β
  | .inl a => .ofFst a
  | .inr b => .ofSnd b

theorem ofPSum_toPSum_leftInverse : Function.LeftInverse (ofPSum: PSum α β → LabelSum α β) (toPSum) := by
  rintro ⟨lb, val⟩
  rcases lb <;> ( dsimp [ofPSum, toPSum, ofFst, ofSnd] )

theorem ofPSum_toPSum_rightInverse : Function.RightInverse (ofPSum: PSum α β → LabelSum α β) (toPSum) := by
  intro ps
  rcases ps <;> ( dsimp [ofPSum, ofFst, ofSnd, toPSum] )


def equivToPSum : LabelSum α β ≃ PSum α β where
  toFun := toPSum
  invFun := ofPSum
  left_inv := ofPSum_toPSum_leftInverse
  right_inv := ofPSum_toPSum_rightInverse

end LabelSum

variable {α β: Sort uh}

inductive Mem (hin: HIntersection α β) : (lb: Label) → (lb.MatchSort α β) → Prop where
  | fst (a: α) (req: ∃(b: β), hin.rel a b) : Mem hin .fst a
  | snd (b: β) (req: ∃(a: α), hin.rel a b) : Mem hin .snd b

--def Mem (hin: HIntersection α β) (lsum: LabelSum α β) : Prop := hin.MemAt lsum.label lsum.val


end HIntersection

end Nemonuri.Relations
