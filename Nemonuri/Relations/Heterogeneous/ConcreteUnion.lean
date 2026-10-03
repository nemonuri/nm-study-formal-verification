module

public import Nemonuri.Relations.Heterogeneous.Union
public import Nemonuri.Relations.Heterogeneous.SeqRel

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh uh2

structure ConcreteUnionStruct (α β: Sort uh) extends toBasic: UnionStruct α β where
  superEquiv: SuperEquivStruct α β
--  decidableRel: DecidableRel (toBasic.rel)


namespace ConcreteUnionStruct

variable {α β: Sort uh}

def getFst (cu: ConcreteUnionStruct α β) : α :=
  match cu.interDiff with
  | .inter a _ => a
  | .ofFst a => a
  | .ofSnd b => cu.superEquiv.invFun b

def getSnd (cu: ConcreteUnionStruct α β) : β :=
  match cu.interDiff with
  | .inter _ b => b
  | .ofFst b => cu.superEquiv.toFun b
  | .ofSnd b => b

variable {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2}

def SeqRel (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnionStruct α1 α2) : (β1 x.getFst) → (β2 x.getSnd) → Prop :=
  Heterogeneous.SeqRel pi.rel x.rel x.getFst x.getSnd
--(domRel: α → β → Prop) (fst: α1) (snd: α2) (y1: β1 fst) (y2: β2 snd)

/-
structure SeqRel (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnionStruct α1 α2) (y1: β1 x.getFst) (y2: β2 x.getSnd) : Prop where
  fst : (∃())
-/

end ConcreteUnionStruct


variable {α β: Sort uh}

structure IsConcreteUnion (s: ConcreteUnionStruct α β) : Prop where
  is_union: IsUnion s.rel s.interDiff
  is_super_equiv: IsSuperEquiv s.rel s.superEquiv

structure ConcreteUnion (α β: Sort uh) extends toStruct: ConcreteUnionStruct α β where
  valid: IsConcreteUnion toStruct


namespace ConcreteUnion

/-
def ofInterDiff (idf: UnionStruct.InterDiff α β) (rel: α → β → Prop) (req: IsUnion rel idf) (dr: DecidableRel rel) (se: SuperEquiv rel) : ConcreteUnion α β where
  rel := rel
  interDiff := idf
  decidableRel := dr
  superEquiv := se.toStruct
  valid := ⟨req, se.valid⟩


def ofUnion (uni: Union α β) (dr: DecidableRel uni.rel) (se: SuperEquiv uni.rel) : ConcreteUnion α β := ofInterDiff uni.interDiff uni.rel uni.valid dr se

def toUnion (cu: ConcreteUnion α β) : Union α β := ⟨⟨cu.rel, cu.interDiff⟩, cu.valid.is_union⟩



--@[match_pattern]
def ofInter (fst: α) (snd: β) (rel: α → β → Prop) (req: rel fst snd) (dr: DecidableRel rel) (se: SuperEquiv rel) : ConcreteUnion α β :=
  ofInterDiff (.inter fst snd) rel (.inter fst snd req) dr se

--@[match_pattern]
def ofDiffFst (fst: α) (rel: α → β → Prop) (se: SuperEquiv rel) (req: ¬rel fst (se.toFun fst)) (dr: DecidableRel rel) : ConcreteUnion α β :=
  ofInterDiff (.ofFst fst) rel (.diff .fst fst (.fst fst (se.valid.isSubOfEquiv.basic.not_rel_of_not_rel req))) dr se

--@[match_pattern]
def ofDiffSnd (snd: β) (rel: α → β → Prop) (se: SuperEquiv rel) (req: ¬rel (se.invFun snd) snd) (dr: DecidableRel rel) : ConcreteUnion α β :=
  ofInterDiff (.ofSnd snd) rel (.diff .snd snd (.snd snd (se.valid.isSubOfEquiv.filp.not_rel_of_not_rel req))) dr se


theorem getFst_getSnd_rel_iff_interDiff_eq {cu: ConcreteUnion α β} : cu.rel cu.getFst cu.getSnd ↔ (cu.interDiff = (.inter cu.getFst cu.getSnd)) := by
  rcases cu with ⟨⟨⟨rel, idf⟩, dr, se1, se2⟩, ⟨lm1, lm2⟩⟩
  dsimp at ⊢ dr lm1 lm2
  rcases idf with ⟨fst, snd⟩ | ⟨lb, val⟩
  · dsimp [ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
    rcases lm1 with ⟨_, _, lm1⟩ | _
    simp only [lm1]
  · rcases lb <;> (dsimp [ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]; simp)
    · rcases lm1 with _ | ⟨_, _, lm1⟩
      rcases lm1 with ⟨_, lm1⟩
      exact lm1 (se1 val)
    · rcases lm1 with _ | ⟨_, _, lm1⟩
      rcases lm1
      rename_i lm1
      exact lm1 (se2 val)
-/





section Seq

variable {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2}

def seqRel (_: ConcreteUnion ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnion α1 α2) (_: β1 x.getFst) (_: β2 x.getSnd) : Prop := x.rel x.getFst x.getSnd

--def seqSuperEquiv


/-
def applyPi (pi: ConcreteUnion ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnion α1 α2) : ConcreteUnion (β1 x.getFst) (β2 x.getSnd) :=
  match pi with
  | ⟨⟨⟨rel, idf⟩, dr, se1, se2⟩, lm1⟩ =>
  match idf with
  | .inter pi1 pi2 =>
    let rel2 (y1: β1 x.getFst) (y2: β2 x.getSnd) : Prop :=
    let y1 := pi1 x.getFst
    let y2 := pi2 x.getSnd
-/

end Seq
    --if lm2: rel y1 y2


end ConcreteUnion


structure ConcretePiUnionStruct (α1 α2: Sort uh) (β1: α1 → Sort uh2) (β2: α2 → Sort uh2) extends toConcrete: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x) where
  sigmaToPi1 (x1: α1) (y1: β1 x1) (x2: α1) : β1 x2
  sigmaToPi2 (x1: α2) (y1: β2 x1) (x2: α2) : β2 x2
  --invPi (x1: α1) (y1: β1 x1) (x2: α2) (y2: β2 x2) : ((x: α1) → β1 x) × ((x: α2) → β2 x)

/-
structure IsConcretePiUnion {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2} (s: ConcretePiUnionStruct α1 α2 β1 β2) : Prop
  extends toConcrete: IsConcreteUnion s.toConcrete where
  sigmaToPi1_valid: s.rel
-/

end Nemonuri.Relations.Heterogeneous

end
