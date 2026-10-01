module

public import Nemonuri.Relations.Heterogeneous.MemAt
public import Nemonuri.Relations.Heterogeneous.IsSub

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

structure IntersectionStruct (α β: Sort uh) where
  rel: α → β → Prop
  fst: α
  snd: β

variable {α β: Sort uh}

namespace IntersectionStruct

def get (i: IntersectionStruct α β) (lb: Label) : lb.MatchSort α β := lb.casesOn i.fst i.snd

@[defeq, simp]
theorem get_fst {i: IntersectionStruct α β} : i.get Label.fst = i.fst := rfl

@[defeq, simp]
theorem get_snd {i: IntersectionStruct α β} : i.get Label.snd = i.snd := rfl

end IntersectionStruct

structure IsIntersection (s: IntersectionStruct α β) where
  is_rel: s.rel s.fst s.snd

structure Intersection (α β: Sort uh) extends toStruct: IntersectionStruct α β where
  valid: IsIntersection toStruct

namespace Intersection

structure ConcreteStruct (α β: Sort uh) extends toBasic: IntersectionStruct α β where
  superFun: α → β
  superFunInv: β → α

structure IsConcrete (s: ConcreteStruct α β) : Prop extends toBasic: IsIntersection s.toBasic where
  subOfEquiv: IsSubOfEquiv s.rel s.superFun s.superFunInv

structure Concrete (α β: Sort uh) extends toStruct: ConcreteStruct α β where
  valid: IsConcrete toStruct

end Intersection



end Nemonuri.Relations.Heterogeneous

end
