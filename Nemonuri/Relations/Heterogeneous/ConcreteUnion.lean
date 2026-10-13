module

public import Nemonuri.Relations.Heterogeneous.Union
public import Nemonuri.Relations.Heterogeneous.SeqRel

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh uh2



structure ConcreteUnionStruct (α β: Sort uh) where
  areRel: α → β → Bool
  superEquiv: SuperEquivStruct α β
  interDiff: UnionStruct.InterDiff α β




--extends toBasic: UnionStruct α β where
--  superEquiv: SuperEquivStruct α β
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

structure Rel (cu: ConcreteUnionStruct α β) (fst: α) (snd: β) : Prop where
  are_rel: cu.areRel fst snd = .true
  fst_eq: fst = cu.superEquiv.invFun snd
  snd_eq: snd = cu.superEquiv.toFun fst

theorem rel_iff_rel_and_eq {cu: ConcreteUnionStruct α β} {fst: α} {snd: β}
  : cu.Rel fst snd ↔ (cu.areRel fst snd = .true ∧ fst = cu.superEquiv.invFun snd ∧ snd = cu.superEquiv.toFun fst) := by
  constructor
  · rintro ⟨lm1, lm2, lm3⟩
    exact ⟨lm1, lm2, lm3⟩
  · rintro ⟨lm1, lm2, lm3⟩
    exact ⟨lm1, lm2, lm3⟩


theorem rel_is_super_equiv {cu: ConcreteUnionStruct α β} : IsSuperEquiv cu.Rel cu.superEquiv := by
  refine ⟨?_, ?_⟩ <;> dsimp [IsSubOfFunction, isSub_def, OfFunction, Function.flip_def]
  · intro a b ⟨lm1, lm2, lm3⟩
    exact lm3.symm
  · intro a b ⟨lm1, lm2, lm3⟩
    exact lm2.symm

theorem fst_eq_iff_rel {cu: ConcreteUnionStruct α β} {fst: α} (req: cu.areRel fst (cu.superEquiv.toFun fst) = .true)
  : (fst = cu.superEquiv.invFun (cu.superEquiv.toFun fst)) ↔ cu.Rel fst (cu.superEquiv.toFun fst) := by
  constructor
  · intro lm1
    exact ⟨req, lm1, rfl⟩
  · rintro ⟨lm1, lm2, lm3⟩
    exact lm2

theorem snd_eq_iff_rel {cu: ConcreteUnionStruct α β} {snd: β} (req: cu.areRel (cu.superEquiv.invFun snd) snd = .true)
  : (snd = cu.superEquiv.toFun (cu.superEquiv.invFun snd)) ↔ cu.Rel (cu.superEquiv.invFun snd) snd := by
  constructor
  · intro lm1
    exact ⟨req, rfl, lm1⟩
  · rintro ⟨lm1, lm2, lm3⟩
    exact lm3

variable {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2}

def seqAreRel (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (ss: SigmaStampProdStruct α1 α2 β1 β2) (x: ConcreteUnionStruct α1 α2) (y1: β1 x.getFst) (y2: β2 x.getSnd) : Bool :=
  (x.areRel x.getFst x.getSnd) && (pi.areRel (ss.fst.stamp _ y1) (ss.snd.stamp _ y2))
/-
  if x.areRel x.getFst x.getSnd = .true then
    match ss with
    | .fst stamp =>
      let pi2 := stamp _ y1
      pi.areRel pi2 (pi.superEquiv.toFun pi2)
    | .snd stamp =>
      let pi2 := stamp _ y2
      pi.areRel (pi.superEquiv.invFun pi2) pi2
  else
    .false
-/

def seqSuperEquivStruct (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (ss: SigmaStampProdStruct α1 α2 β1 β2) (x: ConcreteUnionStruct α1 α2) : SuperEquivStruct (β1 x.getFst) (β2 x.getSnd) where
  toFun y1 := pi.superEquiv.toFun (ss.fst.stamp _ y1) x.getSnd
  invFun y2 := pi.superEquiv.invFun (ss.snd.stamp _ y2) x.getFst
/-
  toFun y1 :=
    match ss with
    | .fst stamp => pi.superEquiv.toFun (stamp _ y1) x.getSnd
    | .snd _ => pi.getSnd x.getSnd
  invFun y2 :=
    match ss with
    | .fst _ => pi.getFst x.getFst
    | .snd stamp => pi.superEquiv.invFun (stamp _ y2) x.getFst
-/

def seqInterDiff (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (ss: SigmaStampProdStruct α1 α2 β1 β2) (x: ConcreteUnionStruct α1 α2) : UnionStruct.InterDiff (β1 x.getFst) (β2 x.getSnd) :=
  match pi with
  | ⟨_, _, idf⟩ =>
  match idf with
  | .inter piFst piSnd => .inter (piFst x.getFst) (piSnd x.getSnd)
  | .ofFst piFst =>
    let pi2 := ss.fst.stamp _ (piFst x.getFst)
    let pi3 := pi.superEquiv.toFun pi2
    if pi.areRel pi2 pi3 then .inter (pi2 x.getFst) (pi3 x.getSnd) else .ofFst (piFst x.getFst)
  | .ofSnd piSnd =>
    let pi2 := ss.snd.stamp _ (piSnd x.getSnd)
    let pi3 := pi.superEquiv.invFun pi2
    if pi.areRel pi3 pi2 then .inter (pi3 x.getFst) (pi2 x.getSnd) else .ofSnd (piSnd x.getSnd)


--def seqInterDiff (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnionStruct α1 α2) : UnionStruct.InterDiff (β1 x.getFst) (β2 x.getSnd) :=

/-


def SeqRel (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnionStruct α1 α2) : (β1 x.getFst) → (β2 x.getSnd) → Prop :=
  Heterogeneous.SeqRel pi.rel x.rel x.getFst x.getSnd
-/
--(domRel: α → β → Prop) (fst: α1) (snd: α2) (y1: β1 fst) (y2: β2 snd)

/-
structure SeqRel (pi: ConcreteUnionStruct ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnionStruct α1 α2) (y1: β1 x.getFst) (y2: β2 x.getSnd) : Prop where
  fst : (∃())
-/

end ConcreteUnionStruct


variable {α β: Sort uh}

structure IsConcreteUnion (s: ConcreteUnionStruct α β) : Prop where
  rel_is_union: IsUnion s.Rel s.interDiff

structure ConcreteUnion (α β: Sort uh) extends toStruct: ConcreteUnionStruct α β where
  valid: IsConcreteUnion toStruct


namespace ConcreteUnion


variable {α1 α2: Sort uh} {β1: α1 → Sort uh2} {β2: α2 → Sort uh2}

protected def seq (pi: ConcreteUnion ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnion α1 α2) (ss: PartialSigmaStampProd x.Rel pi.Rel) : ConcreteUnion (β1 x.getFst) (β2 x.getSnd) where
  areRel := pi.seqAreRel ss.toStruct x.toStruct
  superEquiv := pi.seqSuperEquivStruct ss.toStruct x.toStruct
  interDiff := pi.seqInterDiff ss.toStruct x.toStruct
  valid := by
    rcases pi with ⟨pi, lm1⟩
    rcases x with ⟨a, lm2⟩
    rcases ss with ⟨ss, lm3⟩
    dsimp
    rcases a with ⟨arA, seA, idfA⟩
    rcases lm2 with ⟨lm2⟩
    rcases pi with ⟨arPi, sePi, idfPi⟩
    rcases lm1 with ⟨lm1⟩
    refine .mk ?_
    dsimp at lm2 lm1 lm3 ⊢
    rcases lm2 with ⟨a1, a2, lm2⟩ | ⟨lb, a, lm2⟩
    · specialize lm3 a1 a2
      rcases lm1 with ⟨pi1, pi2, lm1⟩ | ⟨lb, pi, lm1⟩
      · specialize lm3 pi1 pi2 lm2 lm1
        rcases lm3 with ⟨lm3, lm4, lm5⟩
        rcases lm3 with ⟨lm3_1, lm3_2, lm3_3⟩
        rcases lm2 with ⟨lm2_1, lm2_2, lm2_3⟩
        rcases lm1 with ⟨lm1_1, lm1_2, lm1_3⟩
        dsimp at lm3_1 lm3_2 lm3_3 lm2_1 lm2_2 lm2_3 lm1_1 lm1_2 lm1_3 ⊢
        refine .inter _ _ ?_
        refine .mk ?_ ?_ ?_
        · dsimp [ConcreteUnionStruct.seqAreRel, ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
          simp [lm2_1, lm3_1]
        · dsimp [ConcreteUnionStruct.seqSuperEquivStruct, ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
          rw [← lm3_2]
          exact lm4.symm
        · dsimp [ConcreteUnionStruct.seqSuperEquivStruct, ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
          rw [← lm3_3]
          exact lm5.symm
      · rcases lb
        · replace lm1 := lm1.fst_forall_not






/-
protected def seq (pi: ConcreteUnion ((x: α1) → β1 x) ((x: α2) → β2 x)) (ss: SigmaStampProd pi.Rel) (x: ConcreteUnion α1 α2) : ConcreteUnion (β1 x.getFst) (β2 x.getSnd) where
   areRel := pi.seqAreRel ss.toStruct x.toStruct
   superEquiv := pi.seqSuperEquivStruct ss.toStruct x.toStruct
   interDiff := pi.seqInterDiff ss.toStruct x.toStruct
   valid := by
    rcases pi with ⟨pi, lm1⟩
    rcases x with ⟨a, lm2⟩
    rcases ss with ⟨ss, lm3⟩
    rcases lm3 with ⟨lm3_1, lm3_2⟩
    dsimp [isPartialSigmaStamp_def] at lm3_1 lm3_2
    dsimp
    rcases a with ⟨arA, seA, idfA⟩
    rcases lm2 with ⟨lm2⟩
    rcases pi with ⟨arPi, sePi, idfPi⟩
    rcases lm1 with ⟨lm1⟩
    refine .mk ?_
    dsimp at lm2 lm1 ⊢
    rcases lm2 with ⟨a1, a2, lm2⟩ | ⟨lb, a, lm2⟩
    · rcases lm2 with ⟨lm2_1, lm2_2, lm2_3⟩
      dsimp at lm2_1 lm2_2 lm2_3
      subst lm2_3
      rcases lm1 with ⟨pi1, pi2, lm1⟩ | ⟨lb, pi, lm1⟩
      · rcases lm1 with ⟨lm1_1, lm1_2, lm1_3⟩
        dsimp at lm1_1 lm1_2 lm1_3
        subst lm1_3
        refine .inter _ _ ?_
        refine .mk ?_ ?_ ?_
        dsimp [ConcreteUnionStruct.seqAreRel, ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
        simp [lm2_1]
        specialize lm3_1 a1 pi1
        --specialize lm3_2 (seA.toFun a1) (sePi.toFun pi1 (seA.toFun a1))
        rcases lm3_1 with ⟨lm4_1, lm5_1⟩ | ⟨lm4_1⟩
        · rcases lm4_1.fst_req_exists with ⟨pi3_1, ⟨lm6_1, lm7_1, lm8_1⟩⟩
          dsimp at lm6_1 lm7_1 lm8_1
          subst lm8_1
          refine Eq.trans ?_ lm6_1
          congr
          specialize lm3_2 (seA.toFun a1) (sePi.toFun pi1)
          rcases lm3_2 with ⟨lm4_2, lm5_2⟩ | ⟨lm4_2⟩
          · rcases lm4_2.snd_req_exists with ⟨pi3_2, ⟨lm6_2, lm7_2, lm8_2⟩⟩
            dsimp at lm6_2 lm7_2 lm8_2
            subst lm7_2
-/
          --refine funext ?_
          --intro a2
          --specialize lm3_2 a2 (sePi.toFun pi1 a2)
          --rcases lm3_2 with ⟨lm4_2, lm5_2⟩ | ⟨lm4_2⟩
/-
        <;> rcases lm3_2 with ⟨lm4_2, lm5_2⟩ | ⟨lm4_2⟩
        · rcases lm4_1.fst_req_exists with ⟨pi3_1, ⟨lm6_1, lm7_1, lm8_1⟩⟩
          rcases lm4_2.snd_req_exists with ⟨pi3_2, ⟨lm6_2, lm7_2, lm8_2⟩⟩
          dsimp at lm6_1 lm7_1 lm8_1 lm6_2 lm7_2 lm8_2
          subst lm8_1 lm7_2
-/
/-
        refine Eq.trans ?_ lm1_1
        congr
        · refine funext ?_
          intro a2
          have lm4_1 := lm3_1 a1 (pi1 a1)
          have lm4_2 := lm3_1 a2 (pi1 a2)
          rcases lm4_1 with ⟨lm4_1, lm5_1⟩ | ⟨lm4_1⟩
          <;> rcases lm4_2 with ⟨lm4_2, lm5_2⟩ | ⟨lm4_2⟩
          · rcases lm4_1.fst_req_exists with ⟨pi3_1, ⟨lm6_1, lm7_1, lm8_1⟩⟩
            rcases lm4_2.fst_req_exists with ⟨pi3_2, ⟨lm6_2, lm7_2, lm8_2⟩⟩
            dsimp at lm6_1 lm7_1 lm8_1 lm6_2 lm7_2 lm8_2
            subst lm8_1 lm8_2
-/
/-

-/
/-

        · rcases lm4_1.fst_req_exists with ⟨pi3, ⟨lm7, lm8, lm9⟩⟩
          dsimp at lm7 lm8 lm9
          subst lm9
-/
        --· cases lm4_1
        --· rcases lm3_2 with ⟨lm4_2, lm5_2⟩ | ⟨lm4_2⟩
        --  · rw [lm5_1, lm5_2]
/-
        refine .inter _ _ ?_
        dsimp [ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
        refine .mk ?_ ?_ ?_
        · dsimp [ConcreteUnionStruct.seqAreRel, ConcreteUnionStruct.getFst, ConcreteUnionStruct.getSnd]
          simp [lm2_1]
-/
    --
    --dsimp


--def seqInterDiff (pi: ConcreteUnion ((x: α1) → β1 x) ((x: α2) → β2 x)) (x: ConcreteUnion α1 α2) : UnionStruct.InterDiff (β1 x.getFst) (β2 x.getSnd) :=
--  if

/-
protected def seq (pi: ConcreteUnion ((x: α1) → β1 x) ((x: α2) → β2 x)) (ss: SigmaStampProd pi.Rel) (x: ConcreteUnion α1 α2) : ConcreteUnion (β1 x.getFst) (β2 x.getSnd) where
  areRel := pi.seqAreRel ss.toStruct x.toStruct
  superEquiv := pi.seqSuperEquivStruct ss.toStruct x.toStruct
-/
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
