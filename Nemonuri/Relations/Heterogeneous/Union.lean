module

public import Nemonuri.Relations.Heterogeneous.Intersection
public import Nemonuri.Relations.Heterogeneous.SuperEquiv

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh uh2

variable {α β: Sort uh}

inductive UnionStruct.InterDiff (α β: Sort uh) where
  | inter (fst: α) (snd: β)
  | diff (label: Label) (val: label.MatchSort α β)


namespace UnionStruct.InterDiff

@[match_pattern]
def ofFst (a: α) : InterDiff α β := .diff .fst a

@[match_pattern]
def ofSnd (b: β) : InterDiff α β := .diff .snd b

open Label.MatchSort in
inductive Mem (α β: Sort uh) : (InterDiff α β) → (InterDiff (α → Prop) (β → Prop)) → Prop where
  | inter_inter
      (val1: α) (val2: β) (pred1: α → Prop) (pred2: β → Prop) (req: pred1 val1 ∨ pred2 val2)
      : Mem α β (.inter val1 val2) (.inter pred1 pred2)
  | diff_inter
      (lb: Label) (val: lb.MatchSort α β) (pred1: α → Prop) (pred2: β → Prop) (req: mergePred lb pred1 pred2 val)
      : Mem α β (.diff lb val) (.inter pred1 pred2)
  | inter_diff
      (val1: α) (val2: β) (lb: Label) (pred: lb.MatchSort (α → Prop) (β → Prop)) (req: equivOfPred pred (lb.casesOn val1 val2))
      : Mem α β (.inter val1 val2) (.diff lb pred)
  | diff_diff (lb: Label) (val: lb.MatchSort α β) (pred: lb.MatchSort (α → Prop) (β → Prop)) (req: equivOfPred pred val)
      : Mem α β (.diff lb val) (.diff lb pred)

--{α1 α2: Sort uh} (β1: α1 → Sort uh2) (β2: α2 → Sort uh2) (x: ConcreteUnion α1 α2) : Sort uh2
inductive IsMergedMotive {α1 α2: Sort uh} (β1: α1 → Sort uh2) (β2: α2 → Sort uh2) : InterDiff α1 α2 → Sort uh2 → Prop where
  | inter_fst (a1: α1) (a2: α2) : IsMergedMotive β1 β2 (.inter a1 a2) (β1 a1)
  | inter_snd (a1: α1) (a2: α2) : IsMergedMotive β1 β2 (.inter a1 a2) (β2 a2)
  | diff_fst (a1: α1) : IsMergedMotive β1 β2 (.diff .fst a1) (β1 a1)
  | diff_snd (a2: α2) : IsMergedMotive β1 β2 (.diff .snd a2) (β2 a2)

def MergedMotive {α1 α2: Sort uh} (β1: α1 → Sort uh2) (β2: α2 → Sort uh2) (idf: InterDiff α1 α2) := (T: Sort uh2) → (IsMergedMotive β1 β2 idf T) → T

/-
def MergedMotive {α1 α2: Sort uh} (β1: α1 → Sort uh2) (β2: α2 → Sort uh2) (idf: InterDiff α1 α2) : Type uh2 := Subtype (IsMergedMotive β1 β2 idf)
-/

end UnionStruct.InterDiff



structure UnionStruct (α β: Sort uh) where
  rel: α → β → Prop
  interDiff: UnionStruct.InterDiff α β

namespace UnionStruct

variable {α β: Sort uh}

/-
inductive Mem (uni: UnionStruct α β) : (UnionStruct (α → Prop) (β → Prop)) → Prop where
  |
-/

/-
inductive Mem : (Union α β) → (Union (α → Prop) (β → Prop)) → Prop where
  | inter (rel1: α → β → Prop) (fst: α) (snd: β) (req1: rel1 fst snd) (rel2: (α → Prop) → (β → Prop) → Prop)
-/

end UnionStruct


inductive IsUnion (rel: α → β → Prop) : UnionStruct.InterDiff α β → Prop where
  | inter (fst: α) (snd: β) (req: rel fst snd) : IsUnion rel (.inter fst snd)
  | diff (label: Label) (val: label.MatchSort α β) (req: NotMemAt rel label val) : IsUnion rel (.diff label val)

structure Union (α β: Sort uh) extends toStruct: UnionStruct α β where
  valid: IsUnion toStruct.rel toStruct.interDiff


namespace Union

variable {α β: Sort uh}

def ofInter (rel: α → β → Prop) (fst: α) (snd: β) (req: rel fst snd) : Union α β where
  rel := rel
  interDiff := .inter fst snd
  valid := .inter fst snd req

def ofDiff (rel: α → β → Prop) (lb: Label) (x: lb.MatchSort α β) (req: NotMemAt rel lb x) : Union α β where
  rel := rel
  interDiff := .diff lb x
  valid := .diff lb x req

def recInterDiff.{um}
  {motive: Union α β → Sort um}
  (inter: (rel: α → β → Prop) → (fst: α) → (snd: β) → (req: rel fst snd) → motive (.ofInter rel fst snd req))
  (diff: (rel: α → β → Prop) → (lb: Label) → (x: lb.MatchSort α β) → (req: NotMemAt rel lb x) → motive (.ofDiff rel lb x req))
  (t: Union α β)
  : motive t :=
  match t with
  | ⟨⟨rel, idf⟩, lm1⟩ =>
  match idf with
  | .inter fst snd =>
    have lm1: rel fst snd := by dsimp at lm1; rcases lm1; assumption
    inter rel fst snd lm1
  | .diff lb val =>
    have lm1: NotMemAt rel lb val := by dsimp at lm1; rcases lm1; assumption
    diff rel lb val lm1


def ofFst (rel: α → β → Prop) [DecidableRel rel] (f: α → β) (req: IsSubOfFunction rel f) (a: α) : Union α β where
  rel := rel
  interDiff := if rel a (f a) then .inter a (f a) else .ofFst a
  valid := by
    by_cases lm1: rel a (f a) <;> simp [lm1]
    · exact .inter a (f a) lm1
    · have lm2 := req.not_rel_of_not_rel lm1
      exact .diff .fst a (.fst a lm2)

def ofSnd (rel: α → β → Prop) [DecidableRel rel] (f: β → α) (req: IsSubOfFunction (flip rel) f) (b: β) : Union α β where
  rel := rel
  interDiff := if rel (f b) b then .inter (f b) b else .ofSnd b
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

def Mem (uv: Union α β) (upred: Union (α → Prop) (β → Prop)) : Prop := uv.interDiff.Mem α β upred.interDiff




/-
def applyFun.{uh2} {α β: Sort uh} {α2 β2: Sort uh2} (f: Union (α → α2) (β → β2)) (x: Union α β) : Union α2 β2 :=
  match f, x with
-/
  --| .inter f1 f2, .inter v1 v2 =>

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
