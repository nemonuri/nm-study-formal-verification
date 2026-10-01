module

public import Nemonuri.Relations.Heterogeneous.MemAt

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


/-
variable {α β: Sort uh}

structure Intersection (rel: α → β → Prop) where
  fst: α
  snd: β
  valid: rel fst snd

namespace Intersection

variable {rel: α → β → Prop}

def get (i: Intersection rel) (lb: Label) : lb.MatchSort α β := lb.casesOn i.fst i.snd

@[defeq, simp]
theorem get_fst {i: Intersection rel} : i.get Label.fst = i.fst := rfl

@[defeq, simp]
theorem get_snd {i: Intersection rel} : i.get Label.snd = i.snd := rfl

end Intersection

inductive Union (rel: α → β → Prop) where
  | inter (fst: α) (snd: β) (req: rel fst snd)
  | diff (label: Label) (val: label.MatchSort α β) (req: NotMemAt rel label val)
-/


end Nemonuri.Relations.Heterogeneous

end
