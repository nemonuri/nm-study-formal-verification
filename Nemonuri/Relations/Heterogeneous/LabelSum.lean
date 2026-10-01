module

public import Nemonuri.Relations.Heterogeneous.Label
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

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

end Nemonuri.Relations.Heterogeneous

end
