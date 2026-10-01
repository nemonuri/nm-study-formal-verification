module

public import Nemonuri.Relations.Heterogeneous.Intersection

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

variable {α β: Sort uh}

inductive UnionStruct.InterDiff (α β: Sort uh) where
  | inter (fst: α) (snd: β)
  | diff (label: Label) (val: label.MatchSort α β)


namespace UnionStruct.InterDiff

@[match_pattern]
def ofFst (a: α) : InterDiff α β := .diff .fst a

@[match_pattern]
def ofSnd (b: β) : InterDiff α β := .diff .snd b

end UnionStruct.InterDiff



structure UnionStruct (α β: Sort uh) where
  rel: α → β → Prop
  interDiff: UnionStruct.InterDiff α β



inductive IsUnion (rel: α → β → Prop) : UnionStruct.InterDiff α β → Prop where
  | inter (fst: α) (snd: β) (req: rel fst snd) : IsUnion rel (.inter fst snd)
  | diff (label: Label) (val: label.MatchSort α β) (req: NotMemAt rel label val) : IsUnion rel (.diff label val)

structure Union (α β: Sort uh) extends toStruct: UnionStruct α β where
  valid: IsUnion toStruct.rel toStruct.interDiff


namespace Union

structure ConcreteStruct (α β: Sort uh) extends toBasic: UnionStruct α β where
  superFun: α → β
  superFunInv: β → α

structure IsConcrete (s: ConcreteStruct α β) : Prop where
  toBasic: IsUnion s.rel s.toBasic.interDiff
  subOfEquiv: IsSubOfEquiv s.rel s.superFun s.superFunInv

structure Concrete (α β: Sort uh) extends toStruct: ConcreteStruct α β where
  valid: IsConcrete toStruct

end Union


end Nemonuri.Relations.Heterogeneous

end
