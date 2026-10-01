module

public import Nemonuri.Relations.Heterogeneous.Intersection
public import Nemonuri.Relations.Heterogeneous.SuperEquiv

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

variable {α β: Sort uh}

def ofFst (rel: α → β → Prop) [DecidableRel rel] (f: α → β) (req: IsSubOfFunction rel f) (a: α) : Union α β where
  rel := rel
  interDiff := if rel a (f a) then .inter a (f a) else .diff .fst a
  valid := by
    by_cases lm1: rel a (f a) <;> simp [lm1]
    · exact .inter a (f a) lm1
    · have lm2 := req.not_rel_of_not_rel lm1
      exact .diff .fst a (.fst a lm2)

def ofSnd (rel: α → β → Prop) [DecidableRel rel] (f: β → α) (req: IsSubOfFunction (flip rel) f) (b: β) : Union α β where
  rel := rel
  interDiff := if rel (f b) b then .inter (f b) b else .diff .snd b
  valid := by
    by_cases lm1: rel (f b) b <;> simp [lm1]
    · exact .inter (f b) b lm1
    · have lm2 := req.not_rel_of_not_rel lm1
      exact .diff .snd b (.snd b lm2)

def ofLabeled (rel: α → β → Prop) [DecidableRel rel] (se: SuperEquiv rel) (lb: Label) (x: lb.MatchSort α β) : Union α β :=
  match lb with
  | .fst => .ofFst rel se.toFun se.valid.isSubOfEquiv.basic x
  | .snd => .ofSnd rel se.invFun se.valid.isSubOfEquiv.filp x


variable {rel: α → β → Prop} [DecidableRel rel] {se: SuperEquiv rel}

@[defeq]
theorem ofLabeled_fst {x: α} : ofLabeled rel se .fst x = .ofFst rel se.toFun se.valid.isSubOfEquiv.basic x := by dsimp [ofLabeled]

@[defeq]
theorem ofLabeled_snd {x: β} : ofLabeled rel se .snd x = .ofSnd rel se.invFun se.valid.isSubOfEquiv.filp x := by dsimp [ofLabeled]

end Union

/-
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
-/

end Nemonuri.Relations.Heterogeneous

end
