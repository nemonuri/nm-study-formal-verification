module

public import Nemonuri.HasHUnion.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Union

@[expose] public section

set_option autoImplicit false

namespace Nemonuri

abbrev DecidableSetLikeMem (S E: Type*) [SetLike S E] : Type _ := (s: S) → (e: E) → Decidable (e ∈ s)

namespace DecidableSetLikeMem

@[reducible]
def ofFinset (E: Type*) [DecidableEq E] : DecidableSetLikeMem (Finset E) E := fun s e => (inferInstance: Decidable (e ∈ s))

end DecidableSetLikeMem


namespace LiftableEmbedding

protected def id (L: Type*) : LiftableEmbedding L L :=
  let emb : L ↪ L := ⟨id, Function.injective_id⟩
  {
    toEmbedding := emb
    lift lv req := lv
    lift_valid := by
      subst emb
      simp
  }

protected def comp (L R1 R2: Type*) (lhs: LiftableEmbedding R1 R2) (rhs: LiftableEmbedding L R1) : LiftableEmbedding L R2 :=
  let emb : L ↪ R2 := Function.Embedding.mk (lhs.toEmbedding ∘ rhs.toEmbedding) (Function.Injective.comp lhs.toEmbedding.injective rhs.toEmbedding.injective)
  {
    toEmbedding := emb
    lift rv2 req :=
      let rv1 : R1 := lhs.lift rv2 (by
        subst emb
        simp at ⊢ req
        obtain ⟨lv, lm1⟩ := req
        exact Exists.intro _ lm1)
      rhs.lift rv1 (by
        subst emb
        subst rv1
        simp at ⊢ req
        obtain ⟨lv, lm1⟩ := req
        rewrite [Eq.comm] at lm1
        subst lm1
        rewrite [lhs.lift_valid]
        exists lv)
    lift_valid := by
      intro lv
      subst emb
      simp [lhs.lift_valid, rhs.lift_valid]
  }



def pureToFinset (L: Type*) : LiftableEmbedding L (Finset L) :=
  let emb : L ↪ (Finset L) := ⟨fun lv => {lv}, by intro lv1 lv2; simp⟩
  {
    toEmbedding := emb
    lift fs req := fs.choose (fun _ => True) (by
      subst emb
      simp at req
      obtain ⟨lv, lm1⟩ := req
      rewrite [Eq.comm] at lm1
      subst lm1
      simp)
    lift_valid := by
      subst emb
      intro lv
      simp
      rw [Finset.choose_eq_iff]
      simp
  }


/-
def bindToFinset (L R: Type*) [DecidableEq R] (lemb: LiftableEmbedding L (Finset R)) : LiftableEmbedding (Finset L) (Finset R) :=
  let emb: (Finset L) ↪ (Finset R) :=
    Function.Embedding.mk (fun (lfs: Finset L) => lfs.biUnion lemb.toEmbedding) (by
      intro lfs1 lfs2 lm1
      simp at lm1 ⊢
      simp [SetLike.ext_iff] at ⊢ lm1
      intro lv
      conv at lm1 => ext; rw [iff_iff_implies_and_implies]; simp

    )
-/

def mapFinset {L R: Type*} (lemb: LiftableEmbedding L R) : LiftableEmbedding (Finset L) (Finset R) :=
  let emb: (Finset L) ↪ (Finset R) := Function.Embedding.mk (fun (lfs: Finset L) => lfs.map lemb.toEmbedding) (by intro lfs1 lfs2; simp)
  let liftImpl (rfs: Finset R) (req: rfs ∈ Set.range emb) : Finset L :=
    have lm1 (rv) (req2: rv ∈ rfs) : rv ∈ Set.range lemb := by
      subst emb
      simp at req ⊢
      obtain ⟨lv, lm1⟩ := req
      rewrite [Eq.comm] at lm1
      subst lm1
      simp at req2
      rcases req2 with ⟨_,_,lm2⟩
      exact Exists.intro _ lm2
    let liftEmb : { rv // rv ∈ Set.range lemb } ↪ L := Function.Embedding.mk lemb.liftAlt lemb.liftAlt_Injective
    let mapEmb : { rv // rv ∈ rfs } ↪ { rv // rv ∈ Set.range lemb } := Function.Embedding.mk (Subtype.map id lm1) (by intro _ _; simp [Subtype.map_def])
    (rfs.attach.map mapEmb).map liftEmb
  { toEmbedding := emb, lift := liftImpl
    lift_valid lfs := by
      subst liftImpl
      subst emb
      simp [SetLike.ext_iff]
      simp [Subtype.map_def, ← LiftableEmbedding.lift_eq_liftAlt, LiftableEmbedding.lift_valid]
      intro lv _
      exists lv }

theorem mapFinset_mem_iff_mem {L R: Type*} {lemb: LiftableEmbedding L R} {lv: L} {lfs: Finset L}
  : (lemb lv ∈ lemb.mapFinset lfs) ↔ (lv ∈ lfs) := by
  dsimp [coe_eq_toEmbedding_coe, mapFinset]
  exact Finset.mem_map' lemb.toEmbedding

theorem mapFinset_lift_mem_iff {L R: Type*}
  {lemb: LiftableEmbedding L R} {rv: R} (req1: rv ∈ Set.range lemb) {rfs: Finset R} (req2: rfs ∈ Set.range lemb.mapFinset)
  : (lemb.lift rv req1 ∈ lemb.mapFinset.lift rfs req2) ↔ (rv ∈ rfs) := by
  revert req1 req2
  simp
  intro lv lm1 lfs lm2
  rewrite [Eq.comm] at lm1 lm2
  subst lm1 lm2
  dsimp [coe_eq_toEmbedding_coe]
  simp [lift_valid]
  exact mapFinset_mem_iff_mem.symm



end LiftableEmbedding


namespace HasHUnion

section EmbedSetAt

universe u1 u2
variable {L1 L2: Type u1} [HasHUnion.{u1, u2} L1 L2]

def leftSetAt (lb: Label) (ls1: Set L1) (ls2: Set L2) : Set (LeftTypeAt L1 L2 lb) :=
  lb.casesOn (motive := fun lb0 => Set (LeftTypeAt L1 L2 lb0)) ls1 ls2


def RightSet (L1 L2: Type u1) [HasHUnion.{u1, u2} L1 L2] : Type _ := Set (HUnionElemAt L1 L2)


namespace HUnionElemAt

inductive IsInUnion (ls1: Set L1) (ls2: Set L2) (rv: HUnionElemAt L1 L2) : Prop where --(HUnionElemAt L1 L2) →
  | fst (lv: L1) (req1: lv ∈ ls1) (req2: embedAt L1 L2 .fst lv = rv.val) --: IsInUnion ls1 ls2 (.pureFst L1 L2 lv)
  | snd (lv: L2) (req1: lv ∈ ls2) (req2: embedAt L1 L2 .snd lv = rv.val) --: IsInUnion ls1 ls2 (.pureSnd L1 L2 lv)

theorem isInUnion_iff_exists {ls1: Set L1} {ls2: Set L2} {rv: HUnionElemAt L1 L2}
  : (IsInUnion ls1 ls2 rv) ↔ (∃(lb: Label), ∃(lv: LeftTypeAt L1 L2 lb), lv ∈ leftSetAt lb ls1 ls2 ∧ embedAt L1 L2 lb lv = rv.val) := by
  constructor
  · rintro lm1
    rcases lm1 with ⟨lv, lm1, lm2⟩ | ⟨lv, lm1, lm2⟩
    · exists .fst
      exists lv
    · exists .snd
      exists lv
  · rintro ⟨lb, lv, lm1, lm2⟩
    rcases lb
    · exact .fst lv lm1 lm2
    · exact .snd lv lm1 lm2

def decideIsInUnion [DecidableEmbedRange L1 L2] (ls1: Set L1) (ls2: Set L2) [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] (rv: HUnionElemAt L1 L2) : Bool :=
  rv.recDiffInter₂
    (fun lb lv _ => lb.casesOn (fun lv0 => decide (lv0 ∈ ls1)) (fun lv0 => decide (lv0 ∈ ls2)) <| lv)
    (fun rv lm1 =>
      (decide (HasHUnion.liftAt L1 L2 rv .fst (lm1 .fst) ∈ ls1)) || (decide (HasHUnion.liftAt L1 L2 rv .snd (lm1 .snd) ∈ ls2)))
    --(fun rv0 => decide (rv0.lift ∈ ls1))
    --(fun rv0 => decide (rv0.lift ∈ ls2))
    --(fun rv0 => decide (rv0.liftAt .fst ∈ ls1) || decide (rv0.liftAt .snd ∈ ls2))


theorem decideIsInUnion_eq_true_iff_in_union
  [DecidableEmbedRange L1 L2] {ls1: Set L1} {ls2: Set L2} [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] {rv: HUnionElemAt L1 L2}
  : (decideIsInUnion ls1 ls2 rv) ↔ (IsInUnion ls1 ls2 rv) := by
  cases rv using recDiffInter₂
  · rename_i lb lv lm1
    dsimp [decideIsInUnion]
    rw [recDiffInter₂_diff lm1]
    rcases lb
    · simp
      constructor
      · intro lm3
        refine .fst lv lm3 ?_
        exact pureAt_val_eq_embedAt.symm
      · intro lm3
        rcases lm3 with ⟨lv2, lm3, lm4⟩ | ⟨lv2, lm3, lm4⟩
        · simp [pureAt_val_eq_embedAt, embedAt_injective.eq_iff] at lm4
          subst lm4
          exact lm3
        · simp [pureAt_val_eq_embedAt] at lm4
          simp [← lm4] at lm1
    · simp
      constructor
      · intro lm3
        refine .snd lv lm3 ?_
        exact pureAt_val_eq_embedAt.symm
      · intro lm3
        rcases lm3 with ⟨lv2, lm3, lm4⟩ | ⟨lv2, lm3, lm4⟩
        · simp [pureAt_val_eq_embedAt] at lm4
          simp [← lm4] at lm1
        · simp [pureAt_val_eq_embedAt, embedAt_injective.eq_iff] at lm4
          subst lm4
          exact lm3
  · rename_i rv lm1
    dsimp [decideIsInUnion]
    rw [recDiffInter₂_inter lm1]
    simp
    constructor
    · intro lm2
      rcases lm2 with lm2 | lm2
      · refine .fst (HasHUnion.liftAt L1 L2 rv .fst (lm1 .fst)) ?_ ?_
        · exact lm2
        · simp [liftAt_embedAt_eq, ofInter, ofRightType_def]
      · refine .snd (HasHUnion.liftAt L1 L2 rv .snd (lm1 .snd)) ?_ ?_
        · exact lm2
        · simp [liftAt_embedAt_eq, ofInter, ofRightType_def]
    · intro lm3
      rcases lm3 with ⟨lv2, lm3, lm4⟩ | ⟨lv2, lm3, lm4⟩ <;> (
        dsimp [ofInter, ofRightType_def] at lm4
        rewrite [Eq.comm] at lm4
        subst lm4
        simp [embedAt_liftAt_eq] )
      · exact Or.inl lm3
      · exact Or.inr lm3

instance decidableIsInUnion [DecidableEmbedRange L1 L2] {ls1: Set L1} {ls2: Set L2} [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] {rv: HUnionElemAt L1 L2} : Decidable (IsInUnion ls1 ls2 rv) :=
  decidable_of_iff (decideIsInUnion ls1 ls2 rv = .true) decideIsInUnion_eq_true_iff_in_union


theorem pureAt_injective {lb: Label} : Function.Injective (pureAt L1 L2 lb) := by
  intro _ _ lm1
  simp [pureAt_eq_embedAt_mk] at lm1
  exact HasHUnion.embedAt_injective.eq_iff.mp lm1

def embeddingOfPureAt (lb: Label) : LeftTypeAt L1 L2 lb ↪ HUnionElemAt L1 L2 := .mk (pureAt L1 L2 lb) pureAt_injective

def liftableEmbeddingOfPureAt (lb: Label) : LiftableEmbedding (LeftTypeAt L1 L2 lb) (HUnionElemAt L1 L2) where
  toEmbedding := embeddingOfPureAt lb
  lift rv req := rv.liftAt lb (by
    simp [embeddingOfPureAt, Subtype.ext_iff, pureAt_val_eq_embedAt] at req
    simpa [EmbedRangeAt.exists_embedAt_iff] using req)
  lift_valid lv := by
    dsimp [embeddingOfPureAt, HUnionElemAt.liftAt, pureAt_val_eq_embedAt]
    simp [embedAt_liftAt_eq]


end HUnionElemAt


@[reducible]
def ofFinset (L1 L2: Type u1) [HasHUnion.{u1, u2} L1 L2] : HasHUnion (Finset L1) (Finset L2) where
  R := Finset (HUnionElemAt L1 L2)
  fst := (HUnionElemAt.liftableEmbeddingOfPureAt .fst).mapFinset
  snd := (HUnionElemAt.liftableEmbeddingOfPureAt .snd).mapFinset


def decideEmbedRangeOfFinset [HasHUnion.DecidableEmbedRange L1 L2] (lb: Label) (rfs: (HasHUnion.ofFinset L1 L2).R) : Bool :=
  Finset.fold Bool.and .true (fun (rv: HUnionElemAt L1 L2) => DecidableEmbedRange.isInEmbedRangeAt L1 L2 rv.val lb) rfs

section ofFinset


attribute [local instance] ofFinset

open DecidableEmbedRange

scoped instance (priority := low) {lb: Label} : Membership (LeftTypeAt L1 L2 lb) (LeftTypeAt (Finset L1) (Finset L2) lb) where
  mem := lb.casesOn (motive := fun lb0 => (LeftTypeAt (Finset L1) (Finset L2) lb0) → (LeftTypeAt L1 L2 lb0) → Prop)
                    (fun lfs lv => lv ∈ lfs)
                    (fun lfs lv => lv ∈ lfs)

scoped instance (priority := low) : Membership (HUnionElemAt L1 L2) (R (Finset L1) (Finset L2)) where
  mem rfs rv := let rfs' : Finset (HUnionElemAt L1 L2) := rfs; rv ∈ rfs'


theorem ofFinset_leftTypeAt_eq {lb: Label} : LeftTypeAt (Finset L1) (Finset L2) lb = Finset (LeftTypeAt L1 L2 lb) := by
  rcases lb <;> dsimp


open HUnionElemAt LiftableEmbedding in
theorem ofFinset_pureAt_cast_mem_iff_mem {lb: Label} {lv: LeftTypeAt L1 L2 lb} {lfs: Finset (LeftTypeAt L1 L2 lb)}
  : ((pureAt L1 L2 lb lv) ∈ (embedAt (Finset L1) (Finset L2) lb (cast ofFinset_leftTypeAt_eq.symm lfs))) ↔ (lv ∈ lfs) := by
  rcases lb <;> dsimp [LeftTypeAt] at lv lfs ⊢
  dsimp [embedAt, toLiftableEmbeddingAt]
  · exact mapFinset_mem_iff_mem
  · exact mapFinset_mem_iff_mem


open HUnionElemAt in
theorem ofFinset_pureAt_mem_iff_mem_cast {lb: Label} {lv: LeftTypeAt L1 L2 lb} {lfs: LeftTypeAt (Finset L1) (Finset L2) lb}
  : ((pureAt L1 L2 lb lv) ∈ (embedAt (Finset L1) (Finset L2) lb lfs)) ↔ (lv ∈ (cast ofFinset_leftTypeAt_eq lfs)) := by
  have lm1 := @ofFinset_pureAt_cast_mem_iff_mem L1 L2 _ lb lv
  rcases lb <;> (
    dsimp at ⊢ lm1
    exact lm1)


open LiftableEmbedding in
theorem finset_empty_embedAt_eq_finset_empty {lb: Label} : embedAt (Finset L1) (Finset L2) lb (lb.casesOn ∅ ∅) = (∅: Finset (HUnionElemAt L1 L2)) := by
  simp only [HasHUnion.R, SetLike.ext_iff]
  intro rv
  rcases lb <;> (
    dsimp [embedAt, toLiftableEmbeddingAt]
    dsimp [HasHUnion.fst, HasHUnion.snd]
    dsimp [coe_eq_toEmbedding_coe, LiftableEmbedding.mapFinset]
    rfl )



open HUnionElemAt LiftableEmbedding in
theorem liftAt_mem_iff_mem
  {rv: HUnionElemAt L1 L2} {rfs: Finset (HUnionElemAt L1 L2)} {lb: Label}
  (req1: rv.val ∈ EmbedRangeAt L1 L2 lb) (req2: rfs ∈ EmbedRangeAt (Finset L1) (Finset L2) lb)
  : ((liftAt L1 L2 rv lb req1) ∈ (liftAt (Finset L1) (Finset L2) rfs lb req2)) ↔ (rv ∈ rfs) := by
  dsimp [liftAt, toLiftableEmbeddingAt]
  rcases lb <;> (
    dsimp
    refine mapFinset_lift_mem_iff ?_ _
    simp [HUnionElemAt.ext_iff]
    simp [EmbedRangeAt.exists_embedAt_iff] at req1
    dsimp [coe_eq_toEmbedding_coe, liftableEmbeddingOfPureAt, embeddingOfPureAt, pureAt_val_eq_embedAt]
    exact req1 )



/-
  rewrite [EmbedRangeAt.exists_embedAt_iff] at req1 req2
  simp only [Eq.comm] at req1 req2
  rcases req1 with ⟨lv, lm1⟩
  rcases req2 with ⟨lfs, lm2⟩
  rcases rv with ⟨rv, lm3⟩
  dsimp at lm1 ⊢
  subst lm1
  subst lm2
  simp only [embedAt_liftAt_eq]
  dsimp [embedAt, toLiftableEmbeddingAt]
  rcases lb <;> dsimp
  · conv =>
      lhs
      dsimp only [HasHUnion.fst, DFunLike.coe, LiftableEmbedding.mapFinset]
      simp only [Finset.mem_map]
      dsimp [HUnionElemAt.liftableEmbeddingOfPureAt, HUnionElemAt.embeddingOfPureAt]
      simp [HUnionElemAt.ext_iff, HUnionElemAt.pureAt_val_eq_embedAt]
      dsimp [embedAt, toLiftableEmbeddingAt]
      dsimp only [DFunLike.coe]
      simp
  · conv =>
      lhs
      dsimp only [HasHUnion.snd, DFunLike.coe, LiftableEmbedding.mapFinset]
      simp only [Finset.mem_map]
      dsimp [HUnionElemAt.liftableEmbeddingOfPureAt, HUnionElemAt.embeddingOfPureAt]
      simp [HUnionElemAt.ext_iff, HUnionElemAt.pureAt_val_eq_embedAt]
      dsimp [embedAt, toLiftableEmbeddingAt]
      dsimp only [DFunLike.coe]
      simp
-/

theorem finset_not_mem_iff_lift_not_mem
  {rv: HUnionElemAt L1 L2} {rfs: Finset (HUnionElemAt L1 L2)} {lb: Label}
  (req1: rv.val ∈ EmbedRangeAt L1 L2 lb) (req2: rfs ∈ EmbedRangeAt (Finset L1) (Finset L2) lb)
  : ((liftAt L1 L2 rv lb req1) ∉ (liftAt (Finset L1) (Finset L2) rfs lb req2)) ↔ (rv ∉ rfs) :=
  not_iff_not.mpr (liftAt_mem_iff_mem req1 req2)

open HUnionElemAt LiftableEmbedding in
theorem finset_cons
  {rv: HUnionElemAt L1 L2} {rfs: Finset (HUnionElemAt L1 L2)} {lb: Label}
  (req1: rv.val ∈ EmbedRangeAt L1 L2 lb) (req2: rfs ∈ EmbedRangeAt (Finset L1) (Finset L2) lb) (req3: rv ∉ rfs)
  : rfs.cons rv req3 ∈ EmbedRangeAt (Finset L1) (Finset L2) lb := by
  cases rv using indOnPureAt
  rename_i lb2 lv2
  rw [EmbedRangeAt.exists_embedAt_iff] at ⊢
  cases req2 using EmbedRangeAt.indOnLeftTypeEq
  rename_i lfs lm1; subst lm1
  rewrite [pureAt_val_eq_embedAt] at req1
  cases req1 using EmbedRangeAt.indOnLeftTypeEq
  rename_i lv1 lm1
  rewrite [← pureAt_eq_iff_embedAt_eq] at lm1
  have lm2 := req3
  rewrite [lm1, ofFinset_pureAt_mem_iff_mem_cast] at lm2
  rcases lb <;> (
    dsimp [LeftTypeAt] at lm2 lfs lv1
    let lfs2 := lfs.cons lv1 lm2
    exists lfs2
    simp only [lm1, HasHUnion.R, SetLike.ext_iff]
    intro rv
    subst lfs2
    simp
    conv =>
      lhs
      dsimp [embedAt, toLiftableEmbeddingAt, HasHUnion.fst, HasHUnion.snd]
      dsimp [coe_eq_toEmbedding_coe, mapFinset, liftableEmbeddingOfPureAt]
      simp
      dsimp [embeddingOfPureAt]
    conv =>
      rhs
      arg 2
      dsimp [embedAt, toLiftableEmbeddingAt, HasHUnion.fst, HasHUnion.snd]
      dsimp [coe_eq_toEmbedding_coe, mapFinset, liftableEmbeddingOfPureAt]
      simp
      dsimp [embeddingOfPureAt] )



open HUnionElemAt LiftableEmbedding in
theorem decideEmbedRangeOfFinset_eq_true_iff_embed_range_mem [HasHUnion.DecidableEmbedRange L1 L2] {lb: Label} {rfs: R (Finset L1) (Finset L2)}
  : (decideEmbedRangeOfFinset lb rfs = .true) ↔ (rfs ∈ EmbedRangeAt (Finset L1) (Finset L2) lb) := by
  dsimp [decideEmbedRangeOfFinset]
  let de : DecidableEq (LeftTypeAt L1 L2 lb) := fun _ _ => Classical.propDecidable _
  induction rfs using Finset.cons_induction with
  | empty =>
    simp only [Finset.fold_empty, true_iff]
    conv => arg 2; rw [← (@finset_empty_embedAt_eq_finset_empty L1 L2 _ lb)]
    exact EmbedRangeAt.mem_self
  | cons rv rfs lm1 lm2 =>
    simp [Finset.fold_cons]
    conv => lhs; arg 1; rw [isInEmbedRangeAt_eq_true_iff]
    constructor
    · rintro ⟨lm3, lm4⟩
      replace lm4 := lm2.mp lm4
      exact finset_cons lm3 lm4 lm1
    · intro lm3
      cases lm3 using EmbedRangeAt.indOnLeftTypeEq
      rename_i lfs lm3
      simp [HasHUnion.R, SetLike.ext_iff, - Subtype.forall] at lm3
      rcases lb <;> (
        conv at lm3 =>
          ext x
          arg 2
          dsimp [embedAt, toLiftableEmbeddingAt, HasHUnion.fst, HasHUnion.snd]
          dsimp [coe_eq_toEmbedding_coe, mapFinset, liftableEmbeddingOfPureAt]
          simp only [Finset.mem_map]
          dsimp [embeddingOfPureAt]
        dsimp [LeftTypeAt] at lfs
        have lm5 := lm3
        specialize lm3 rv
        simp at lm3
        rcases lm3 with ⟨lv, lm3, lm4⟩
        rewrite [Eq.comm] at lm4
        subst lm4
        simp [pureAt_val_eq_embedAt]
        simp [EmbedRangeAt.exists_embedAt_iff] at lm2
        refine lm2.mpr ?_
        clear lm2
        simp [HasHUnion.R, SetLike.ext_iff, - Subtype.forall]
        dsimp [embedAt, toLiftableEmbeddingAt, HasHUnion.fst, HasHUnion.snd]
        dsimp [coe_eq_toEmbedding_coe, mapFinset, liftableEmbeddingOfPureAt]
        simp only [Finset.mem_map]
        dsimp [embeddingOfPureAt]
        exists (lfs.erase lv)
        intro rv
        specialize lm5 rv
        constructor
        · rintro ⟨lv2, lm6, lm7⟩
          obtain ⟨lm6_1, lm6_2⟩ := Finset.mem_erase.mp lm6; clear lm6
          rewrite [Eq.comm] at lm7
          subst lm7
          simp [pureAt_injective.eq_iff] at lm5
          replace lm5 := lm5.mpr lm6_2
          rcases lm5 with lm5 | lm5
          · exact lm6_1 lm5 |> False.elim
          · exact lm5
        · intro lm6
          simp [lm6] at lm5
          obtain ⟨lv2, lm5, lm7⟩ := lm5
          rewrite [Eq.comm] at lm7
          subst lm7
          simp [pureAt_injective.eq_iff]
          simp [lm5]
          intro lm7
          subst lm7
          exact lm1 lm6 |> False.elim )




end ofFinset

/-
open DecidableEmbedRange in
theorem decideEmbedRangeOfFinset_eq_true_iff_embed_range_mem [HasHUnion.DecidableEmbedRange L1 L2] {lb: Label} {rfs: (HasHUnion.ofFinset L1 L2).R}
  : (decideEmbedRangeOfFinset lb rfs = .true) ↔ (rfs ∈ (@EmbedRangeAt (Finset L1) (Finset L2) (HasHUnion.ofFinset L1 L2) lb)) := by
  let hu : HasHUnion (Finset L1) (Finset L2) := HasHUnion.ofFinset L1 L2
  dsimp [HasHUnion.R] at rfs
  dsimp [decideEmbedRangeOfFinset]
  induction rfs using Finset.cons_induction with
  | empty =>
    simp only [Finset.fold_empty, true_iff]
    --let leftEmpty : Finset (LeftTypeAt L1 L2 lb) := lb.casesOn ∅ ∅
    rcases lb
    · have lm1 : (HUnionElemAt.pureAt (Finset L1) (Finset L2) .fst ∅).val = (∅: Finset (HUnionElemAt L1 L2)) := by
        simp [HUnionElemAt.pureAt_val_eq_embedAt]
-/


--def deciablemem_ : HasHUnion.DecidableEmbedRange L1 L2


namespace RightSet

def ofHUnionSet (s: Set (HUnionElemAt L1 L2)) : RightSet L1 L2 := s

def toHUnionSet (rs: RightSet L1 L2) : Set (HUnionElemAt L1 L2) := rs

instance toUnion : Union (RightSet L1 L2) where
  union rs1 rs2 := ofHUnionSet (rs1.toHUnionSet ∪ rs2.toHUnionSet)

@[defeq]
theorem union_def {rs1 rs2: RightSet L1 L2} : (rs1 ∪ rs2) = ofHUnionSet (rs1.toHUnionSet ∪ rs2.toHUnionSet) := rfl

instance toMembership : Membership (HUnionElemAt L1 L2) (RightSet L1 L2) where
  mem rs re := re ∈ rs.toHUnionSet

@[defeq]
theorem mem_def {rs: RightSet L1 L2} {re: HUnionElemAt L1 L2} : (re ∈ rs) = (re ∈ rs.toHUnionSet) := rfl

def pureAt (lb: Label) (s: Set (LeftTypeAt L1 L2 lb)) : RightSet L1 L2 := s.image (HUnionElemAt.pureAt L1 L2 lb)


theorem pureAt_injective {lb: Label} : Function.Injective (pureAt lb: Set (LeftTypeAt L1 L2 lb) → RightSet L1 L2) := by
  intro s1 s2 lm1
  dsimp [pureAt, RightSet] at lm1
  simp [Set.ext_iff] at lm1 ⊢
  intro lv
  specialize lm1 (HUnionElemAt.pureAt L1 L2 lb lv)
  simp [HUnionElemAt.pureAt_eq_embedAt_mk, embedAt_injective.eq_iff, hunionSetUnivAt_mem_iff_embedRangeAt_mem] at lm1
  exact lm1 lb EmbedRangeAt.mem_self

theorem pureAt_injective_at (lb: Label) : Function.Injective (pureAt lb: Set (LeftTypeAt L1 L2 lb) → RightSet L1 L2) := pureAt_injective

theorem pureAt_pureAt_mem_iff_mem {lb: Label} {s: Set (LeftTypeAt L1 L2 lb)} {lv: LeftTypeAt L1 L2 lb} --{re: HUnionElemAt L1 L2}
  : (HUnionElemAt.pureAt L1 L2 lb lv ∈ (pureAt lb s)) ↔ (lv ∈ s) := by
  dsimp [mem_def, HUnionElemAt.pureAt_eq_embedAt_mk, toHUnionSet]
  constructor
  · intro lm1
    simp [pureAt, HUnionElemAt.pureAt_eq_embedAt_mk, embedAt_injective.eq_iff] at lm1
    exact lm1
  · intro lm1
    simp [pureAt, HUnionElemAt.pureAt_eq_embedAt_mk, embedAt_injective.eq_iff]
    exact lm1

/-
theorem pureAt_ofRightType_mem_iff_liftAt_mem {lb: Label} {s: Set (LeftTypeAt L1 L2 lb)} {rv: R L1 L2} (req: rv ∈ EmbedRangeAt L1 L2 lb)
  : (HUnionElemAt.ofRightType rv (hunionSetUnivAt_mem_of_embedRangeAt_mem req) ∈ (pureAt lb s)) ↔ (liftAt L1 L2 rv lb req ∈ s) := by
  conv =>
    rhs
    rw [← pureAt_pureAt_mem_iff_mem, HUnionElemAt.pureAt_eq_embedAt_mk]
    simp only [liftAt_embedAt_eq]
    rw [← HUnionElemAt.ofRightType_def]
-/

theorem pureAt_mem_iff {lb: Label} {s: Set (LeftTypeAt L1 L2 lb)} {rv: HUnionElemAt L1 L2}
  : (rv ∈ (pureAt lb s)) ↔ (∃(req: rv.val ∈ EmbedRangeAt L1 L2 lb), (liftAt L1 L2 rv.val lb req) ∈ s) := by
  dsimp [mem_def, toHUnionSet]
  simp [pureAt, EmbedRangeAt.exists_embedAt_iff]
  constructor
  · rintro ⟨lv, lm1, lm2⟩
    rewrite [Eq.comm] at lm2
    subst lm2
    simp [HUnionElemAt.pureAt_val_eq_embedAt, embedAt_liftAt_eq]
    exact lm1
  · rintro ⟨⟨lv, lm1⟩, lm2⟩
    exists lv
    simp [← lm1, embedAt_liftAt_eq] at lm2
    refine ⟨lm2, ?_⟩
    simp [HUnionElemAt.pureAt_eq_embedAt_mk, lm1]


/-
  constructor
  · intro lm1
    simp [pureAt] at lm1
-/
    --rewrite [Set.mem_image]


def hunion (ls1: Set L1) (ls2: Set L2) : RightSet L1 L2 := ofHUnionSet { rv | HUnionElemAt.IsInUnion ls1 ls2 rv } --(pureAt .fst ls1) ∪ (pureAt .snd ls2)

/-
theorem hunion_mem_iff_exists {ls1: Set L1} {ls2: Set L2} {rv: HUnionElemAt L1 L2}
  : (rv ∈ hunion ls1 ls2) ↔ (∃(lb: Label), ∃(req: rv.val ∈ EmbedRangeAt L1 L2 lb), (liftAt L1 L2 rv lb req) ∈ (leftSetAt lb ls1 ls2)) := by
  dsimp [hunion, union_def, ofHUnionSet, toHUnionSet, mem_def]
  constructor
  · intro lm1
    rewrite [Set.mem_union] at lm1
    rcases lm1 with lm1 | lm1
    · exists Label.fst
      dsimp [leftSetAt]
      exact pureAt_mem_iff.mp lm1
    · exists Label.snd
      dsimp [leftSetAt]
      exact pureAt_mem_iff.mp lm1
  · rintro ⟨lb, lm1⟩
    rewrite [← pureAt_mem_iff] at lm1
    rw [Set.mem_union]
    rcases lb <;> dsimp [leftSetAt] at lm1
    · exact Or.inl lm1
    · exact Or.inr lm1
-/


end RightSet



end EmbedSetAt

universe u1 u2 u3
variable {LS1 LS2: Type u1} {L1 L2: Type u2} [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2]

structure SetLikeProd (LS1 LS2: Type u1) (L1 L2: Type u2) [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2] where
  fst: LS1
  snd: LS2



namespace SetLikeProd

def decideMem [DecidableEmbedRange L1 L2] (s: SetLikeProd LS1 LS2 L1 L2) [DecidablePred (· ∈ s.fst)] [DecidablePred (· ∈ s.snd)] (rv: HUnionElemAt L1 L2) : Bool :=
  HUnionElemAt.decideIsInUnion s.fst s.snd rv

theorem decideMem_eq_true_iff_in_union
  [DecidableEmbedRange L1 L2] {s: SetLikeProd LS1 LS2 L1 L2}
  [DecidablePred (· ∈ s.fst)] [DecidablePred (· ∈ s.snd)] {rv: HUnionElemAt L1 L2}
  : (s.decideMem rv = .true) ↔ HUnionElemAt.IsInUnion s.fst s.snd rv := by
  dsimp [decideMem]
  simp [HUnionElemAt.decideIsInUnion_eq_true_iff_in_union]

open HUnionElemAt

def AreUnionEquiv (p1 p2: SetLikeProd LS1 LS2 L1 L2) : Prop := ∀⦃rv: HUnionElemAt L1 L2⦄, IsInUnion p1.fst p1.snd rv ↔ IsInUnion p2.fst p2.snd rv


namespace AreUnionEquiv

theorem mk {p1 p2: SetLikeProd LS1 LS2 L1 L2} (req: ∀(rv: HUnionElemAt L1 L2), IsInUnion p1.fst p1.snd rv ↔ IsInUnion p2.fst p2.snd rv) : AreUnionEquiv p1 p2 := req

theorem equivalence : Equivalence (AreUnionEquiv: SetLikeProd LS1 LS2 L1 L2 → SetLikeProd LS1 LS2 L1 L2 → Prop) where
  refl x := by intro x; rfl
  symm := by
    intro x y lm1 rv
    specialize @lm1 rv
    exact lm1.symm
  trans := by
    intro x y z lm1 lm2 rv
    specialize @lm1 rv
    specialize @lm2 rv
    exact Iff.trans lm1 lm2


@[reducible]
def setoidOf (LS1 LS2: Type u1) (L1 L2: Type u2) [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2] : Setoid (SetLikeProd LS1 LS2 L1 L2) where
  r p1 p2 := AreUnionEquiv p1 p2
  iseqv := equivalence


--def decideOf (p1 p2: SetLikeProd LS1 LS2 L1 L2) : Bool := decide (IsInUnion p1.fst p1.snd )



end AreUnionEquiv

/-
def ofFinset (rfs: (HasHUnion.ofFinset L1 L2).R) : SetLikeProd LS1 LS2 L1 L2 where
  fst := Finset.fil
-/

end SetLikeProd

def SetLikeUnion (LS1 LS2: Type u1) (L1 L2: Type u2) [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2] : Type _ := Quotient (SetLikeProd.AreUnionEquiv.setoidOf LS1 LS2 L1 L2)

namespace SetLikeUnion

def mk (sp: SetLikeProd LS1 LS2 L1 L2) : SetLikeUnion LS1 LS2 L1 L2 := Quotient.mk _ sp

@[elab_as_elim]
theorem ind
  {motive: SetLikeUnion LS1 LS2 L1 L2 → Prop}
  (h: (sp: SetLikeProd LS1 LS2 L1 L2) → motive (.mk sp))
  (t: SetLikeUnion LS1 LS2 L1 L2)
  : motive t := by
  cases t using Quotient.ind
  rename_i sp
  specialize h sp
  dsimp [mk] at h
  exact h

def liftOn
  {β: Sort*} (su: SetLikeUnion LS1 LS2 L1 L2)
  (f: SetLikeProd LS1 LS2 L1 L2 → β)
  (c: ∀(sp1 sp2: SetLikeProd LS1 LS2 L1 L2), sp1.AreUnionEquiv sp2 → f sp1 = f sp2)
  : β :=
  Quotient.liftOn su f c

theorem mk_eq_iff {sp1 sp2: SetLikeProd LS1 LS2 L1 L2} : (mk sp1 = mk sp2) ↔ sp1.AreUnionEquiv sp2 := by
  dsimp [mk]
  constructor
  · intro lm1
    exact Quotient.eq_iff_equiv.mp lm1
  · intro lm1
    exact Quotient.sound lm1


variable [DecidableSetLikeMem LS1 L1] [DecidableSetLikeMem LS2 L2] [DecidableEmbedRange L1 L2]


def decideMem (s: SetLikeUnion LS1 LS2 L1 L2) (rv: HUnionElemAt L1 L2) : Bool :=
  s.liftOn (fun sp => sp.decideMem rv) (by
    intro sp1 sp2 lm1
    dsimp [SetLikeProd.decideMem]
    rw [Bool.eq_iff_iff]
    simp [HUnionElemAt.decideIsInUnion_eq_true_iff_in_union]
    exact @lm1 rv)

theorem decideMem_eq_true_iff {s: SetLikeProd LS1 LS2 L1 L2} {rv: HUnionElemAt L1 L2}
  : (decideMem (mk s) rv = .true) ↔ HUnionElemAt.IsInUnion s.fst s.snd rv := by
  dsimp [decideMem]
  simp [← SetLikeProd.decideMem_eq_true_iff_in_union, mk]
  dsimp [liftOn]
  refine Quotient.liftOn_mk _ _ s


def toRightSet (s: SetLikeUnion LS1 LS2 L1 L2) : Set (HUnionElemAt L1 L2) := { rv | s.decideMem rv = .true }


theorem toRightSet_injective : Function.Injective (toRightSet: SetLikeUnion LS1 LS2 L1 L2 → Set (HUnionElemAt L1 L2)) := by
  intro s1 s2 lm1
  cases s1 using SetLikeUnion.ind
  cases s2 using SetLikeUnion.ind
  rename_i sp1 sp2
  simp [- Subtype.forall, Set.ext_iff, toRightSet, decideMem_eq_true_iff] at lm1
  rw [mk_eq_iff]
  intro rv
  exact lm1 rv

instance toSetLike : SetLike (SetLikeUnion LS1 LS2 L1 L2) (HUnionElemAt L1 L2) where
  coe x := x.toRightSet
  coe_injective := toRightSet_injective






end SetLikeUnion


class HasSetLike.{u4} (L1 L2 : Type u2) [HasHUnion.{u2, u3} L1 L2] [DecidableEmbedRange L1 L2] where
  LS1: Type u1
  leftSetLike1: SetLike LS1 L1
  decidableLeftSetLikeMem1: DecidableSetLikeMem LS1 L1
  LS2: Type u1
  leftSetLike2: SetLike LS2 L2
  decidableLeftSetLikeMem2: DecidableSetLikeMem LS2 L2
  leftSetHasHUnion: HasHUnion.{u1, u4} LS1 LS2
  protected coe: (R LS1 LS2) → SetLikeUnion LS1 LS2 L1 L2
  coe_injective: Function.Injective coe

attribute [reducible, instance] HasSetLike.leftSetLike1 HasSetLike.leftSetLike2 HasSetLike.leftSetHasHUnion
                                HasSetLike.decidableLeftSetLikeMem1 HasSetLike.decidableLeftSetLikeMem2
attribute [coe] HasSetLike.coe

namespace HasSetLike

universe u4

abbrev RS (L1 L2 : Type u2) [HasHUnion.{u2, u3} L1 L2] [DecidableEmbedRange L1 L2] [HasSetLike.{u1, u2, u3, u4} L1 L2] : Type _ := (HasSetLike.leftSetHasHUnion: HasHUnion (HasSetLike.LS1 L1 L2) (HasSetLike.LS2 L1 L2)).R

abbrev SetLikeUnionType (L1 L2 : Type u2) [HasHUnion.{u2, u3} L1 L2] [DecidableEmbedRange L1 L2] [HasSetLike.{u1, u2, u3, u4} L1 L2] : Type _ := SetLikeUnion (HasSetLike.LS1 L1 L2) (HasSetLike.LS2 L1 L2) L1 L2

variable [DecidableEmbedRange L1 L2] [HasSetLike.{u1, u2, u3, u4} L1 L2]

instance : CoeOut (RS L1 L2) (SetLikeUnionType L1 L2) where
  coe rs := HasSetLike.coe rs


instance toSetLike : SetLike (RS L1 L2) (HUnionElemAt L1 L2) where
  coe rs := ((rs: SetLikeUnionType L1 L2): Set (HUnionElemAt L1 L2))
  coe_injective := SetLike.coe_injective.comp HasSetLike.coe_injective

/-
@[reducible]
def ofFinset (L1 L2 : Type u2) [HasHUnion.{u2, u3} L1 L2] [DecidableEmbedRange L1 L2] [HasSetLike.{u1, u2, u3, u4} L1 L2] [DecidableEq L1] [DecidableEq L2] : HasSetLike L1 L2 where
  LS1 := Finset L1
  leftSetLike1 := inferInstance
  decidableLeftSetLikeMem1 := DecidableSetLikeMem.ofFinset L1
  LS2 := Finset L2
  leftSetLike2 := inferInstance
  decidableLeftSetLikeMem2 := DecidableSetLikeMem.ofFinset L2
  leftSetHasHUnion := HasHUnion.ofFinset L1 L2
  coe rfs :=
-/


end HasSetLike

/-
namespace RightSet

namespace HUnionSetLikeProd

variable [DecidableEmbedRange L1 L2]

open DecidableEmbedRange


def decideMem (ls1: LS1) (ls2: LS2) [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] (rv: HUnionElemAt L1 L2) : Bool := --Decidable (er ∈ ofSetLikeHUnion ls1 ls2)
  rv.recDiffInter
    (fun rv0 => decide (rv0.lift ∈ ls1))
    (fun rv0 => decide (rv0.lift ∈ ls2))
    (fun rv0 => decide (rv0.liftAt .fst ∈ ls1) || decide (rv0.liftAt .snd ∈ ls2))

theorem decideMem_eq_true_iff_hunionSetLike_mem {ls1: LS1} {ls2: LS2} [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] {rv: HUnionElemAt L1 L2}
  : (decideMem ls1 ls2 rv = .true) ↔ (rv ∈ hunionSetLike ls1 ls2) := by
  dsimp [hunionSetLike, mem_def, toHUnionSet, hunion, union_def, ofHUnionSet]
  simp only [Set.mem_union]
  dsimp [decideMem]
  cases rv using HUnionElemAt.recDiffInter <;> rename_i rv
  · simp
    rcases rv with ⟨rv, lm1⟩
    simp [hdiffSetUnivAt_mem_iff_embedRangAt_mem, EmbedRangeAt.exists_embedAt_iff] at lm1
    rcases lm1 with ⟨⟨lv, lm1⟩, lm2⟩
    rewrite [Eq.comm] at lm1
    subst lm1
    dsimp [Label.toDual] at lm2
    simp [HDiffElemAt.toUnion, pureAt, HUnionElemAt.pureAt_eq_embedAt_mk, embedAt_injective.eq_iff]
    simp [HDiffElemAt.lift, embedAt_liftAt_eq]
    intro x lm3 lm4
    exact lm2 x lm4 |>.elim
  · simp
    rcases rv with ⟨rv, lm1⟩
    simp [hdiffSetUnivAt_mem_iff_embedRangAt_mem, EmbedRangeAt.exists_embedAt_iff] at lm1
    rcases lm1 with ⟨⟨lv, lm1⟩, lm2⟩
    rewrite [Eq.comm] at lm1
    subst lm1
    dsimp [Label.toDual] at lm2
    simp [HDiffElemAt.toUnion, pureAt, HUnionElemAt.pureAt_eq_embedAt_mk, embedAt_injective.eq_iff]
    simp [HDiffElemAt.lift, embedAt_liftAt_eq]
    intro x lm3 lm4
    exact lm2 x lm4 |>.elim
  · simp
    rcases rv with ⟨rv, lm1⟩
    simp [hinterSetUnivAt_mem_iff_embedRangeAt_mem, EmbedRangeAt.exists_embedAt_iff] at lm1
    obtain ⟨lv, lm2⟩ := lm1 .fst
    rewrite [Eq.comm] at lm2
    subst lm2
    obtain ⟨lv2, lm2⟩ := lm1 .snd
    dsimp [HInterElemAt.liftAt]
    conv => lhs; arg 2; simp only [← lm2]
    simp [embedAt_liftAt_eq]
    simp [pureAt, HUnionElemAt.pureAt_eq_embedAt_mk, HInterElemAt.toUnion]
    conv => rhs; arg 2; simp only [← lm2]
    simp [embedAt_injective.eq_iff]



def ofDecidableMem (ls1: LS1) (ls2: LS2) [DecidablePred (· ∈ ls1)] [DecidablePred (· ∈ ls2)] : HUnionSetLikeProd LS1 LS2 L1 L2 where
  fst := ls1
  snd := ls2
  toDecidableMem er := decidable_of_iff (decideMem ls1 ls2 er = .true) decideMem_eq_true_iff_hunionSetLike_mem


def toRightSet (x: HUnionSetLikeProd LS1 LS2 L1 L2) : RightSet L1 L2 := ofHUnionSet { rv | (x.toDecidableMem rv).decide = .true }

theorem toRightSet_injective : Function.Injective (toRightSet: HUnionSetLikeProd LS1 LS2 L1 L2 → RightSet L1 L2) := by
  intro x1 x2 lm1
  dsimp [toRightSet, ofHUnionSet] at lm1
  simp at lm1
  replace lm1 := Set.ext_iff.mp lm1
  dsimp [hunionSetLike] at lm1
  simp only [hunion_mem_iff_exists] at lm1
  rcases x1 with ⟨fst1, snd1, tdm1⟩
  rcases x2 with ⟨fst2, snd2, tdm2⟩
  simp [- Subtype.forall] at lm1 ⊢
  refine ⟨?_, ?_, ?_⟩
  · simp only [SetLike.ext_iff]
    intro lv
    specialize lm1 (HUnionElemAt.pureAt L1 L2 .fst lv)
    simp [HUnionElemAt.pureAt_val_eq_embedAt] at lm1
    rcases lm1 with ⟨lm2, lm3⟩
    simp at lm2 lm3
    simp [Label.forall_iff_fst_and_snd, embedAt_liftAt_eq, leftSetAt] at lm2 lm3
    simp [Label.exists_iff_fst_or_snd, embedAt_liftAt_eq] at lm2 lm3
    rcases lm2 with ⟨lm2_1, lm2_2⟩
    rcases lm3 with ⟨lm3_1, lm3_2⟩
    constructor
    · clear lm3_1 lm3_2
      intro lm1
      simp [lm1] at lm2_1 --lm3_1 lm3_2; clear lm3_1 lm3_2
      rcases lm2_1 with lm2_1 | lm2_1
      · exact lm2_1
      · rcases lm2_1 with ⟨lm4, lm5⟩
        revert lm4
        simp [EmbedRangeAt.exists_embedAt_iff]
        intro lv2 lm4 lm5
        simp [← lm4, embedAt_liftAt_eq] at lm5
        clear lm2_2


end HUnionSetLikeProd

end RightSet
-/

--def RightSet : Type _ := Set (R L1 L2)

/-
def SetOfSetLikeHUnion (ls1: LS1) (ls2: LS2) : Set (R L1 L2) := (embedSetAt .fst (ls1: Set L1)) ∪ (embedSetAt .snd (ls2: Set L2))

structure UnionMemDecidableProd (LS1 LS2: Type u1) (L1 L2: Type u2) [SetLike LS1 L1] [SetLike LS2 L2] [HasHUnion.{u2, u3} L1 L2] where
  fst: LS1
  snd: LS2
  toDecidableUnionMem (elemR: R L1 L2) : Decidable (elemR ∈ SetOfSetLikeHUnion fst snd)
-/



end Nemonuri.HasHUnion

end
