module

public import Nemonuri.TransitionSystemLike.ProgramGraph.Basic
public import Nemonuri.HasHUnion

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 40

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.ProgramGraph

universe uvar_l uval_l uec_l uvar_r uval_r uec_r

open HasHUnion

namespace EvalLike

section LeftEvalAt

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l}
         [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] [HasHUnion Var1 Var2] [HasHUnion Val1 Val2]

scoped instance {lb: Label} : EvalLike (lb.casesOn EC1 EC2) (LeftTypeAt Var1 Var2 lb) (LeftTypeAt Val1 Val2 lb) where
  coe := lb.casesOn
          (motive := fun lb0 => (lb0.casesOn EC1 EC2) → Eval (LeftTypeAt Var1 Var2 lb0) (LeftTypeAt Val1 Val2 lb0))
          (fun x => x)
          (fun x => x)
  coe_injective := by cases lb <;> ( exact EvalLike.coe_injective )

def leftEvalAt (ec1: EC1) (ec2: EC2) (lb: Label) : lb.casesOn EC1 EC2 := lb.casesOn ec1 ec2

variable {ec1: EC1} {ec2: EC2}

@[defeq]
theorem leftEvalAt_def {lb: Label} : leftEvalAt ec1 ec2 lb = lb.casesOn ec1 ec2 := rfl

@[defeq]
theorem leftEvalAt_fst : leftEvalAt ec1 ec2 .fst = ec1 := rfl

@[defeq]
theorem leftEvalAt_snd : leftEvalAt ec1 ec2 .snd = ec2 := rfl

end LeftEvalAt

structure IsInterleaving
  {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l}
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  (op: EC1 → EC2 → (HUnionElemAt Var1 Var2) → (HUnionElemAt Val1 Val2)) : Prop where
  diff (ec1: EC1) (ec2: EC2) (lb: Label) (x: HDiffElemAt Var1 Var2 lb) :
    embedAt Val1 Val2 lb ((leftEvalAt ec1 ec2 lb: (LeftTypeAt Var1 Var2 lb) → (LeftTypeAt Val1 Val2 lb)) x.lift) = (op ec1 ec2 (x.toUnion)).val
  inter (ec1: EC1) (ec2: EC2) (x: HInterElemAt Var1 Var2) :
    ∃(lb: Label), embedAt Val1 Val2 lb ((leftEvalAt ec1 ec2 lb: (LeftTypeAt Var1 Var2 lb) → (LeftTypeAt Val1 Val2 lb)) (x.liftAt lb)) = (op ec1 ec2 (x.toUnion)).val

structure Interleaving
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)] where
  op: EC1 → EC2 → ECR
  valid: IsInterleaving (fun ec1 ec2 => op ec1 ec2)

namespace Interleaving

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} {ECR: Type uec_r}
         [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)]

structure EmbeddableStruct
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)] where
  op: EC1 → EC2 → ECR
  emptyAt (lb: Label) : lb.casesOn EC1 EC2

namespace EmbeddableStruct

def embedAt (s: EmbeddableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR) (lb: Label) : (lb.casesOn EC1 EC2) → ECR :=
  lb.casesOn (motive := fun lb0 => lb0.casesOn EC1 EC2 → ECR)
             (fun ec1 => s.op ec1 (s.emptyAt .snd))
             (fun ec2 => s.op (s.emptyAt .fst) ec2)

variable {s: EmbeddableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR}

@[defeq]
theorem embedAt_fst {ec1: EC1} : s.embedAt .fst ec1 = s.op ec1 (s.emptyAt .snd) := rfl

@[defeq]
theorem embedAt_snd {ec2: EC2} : s.embedAt .snd ec2 = s.op (s.emptyAt .fst) ec2 := rfl

end EmbeddableStruct

structure IsEmbeddable (s: EmbeddableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR) : Prop where
  interleave: IsInterleaving (fun ec1 ec2 => s.op ec1 ec2)
  embed_eq (lb: Label) (ec: lb.casesOn EC1 EC2) (varL: LeftTypeAt Var1 Var2 lb) :
    embedAt Val1 Val2 lb ((ec: (LeftTypeAt Var1 Var2 lb) → (LeftTypeAt Val1 Val2 lb)) varL) = ((s.embedAt lb ec) (.pureAt Var1 Var2 lb varL)).val

namespace IsEmbeddable

open EmbeddableStruct

variable {s: EmbeddableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR}

theorem embedAt_injective (h: IsEmbeddable s) {lb: Label} : Function.Injective (s.embedAt lb) := by
  let huVar : HasHUnion Var1 Var2 := inferInstance
  let huVal : HasHUnion Val1 Val2 := inferInstance
  rcases h with ⟨⟨lm1, lm2⟩, lm3⟩
  replace lm1 := fun ec1 ec2 => lm1 ec1 ec2 lb
  specialize lm3 lb
  cases lb
  · dsimp [Function.Injective, embedAt_fst]
    intro ecL1 ecL2 lm4
    simp only [← DFunLike.coe_injective.eq_iff, funext_iff] at lm4 ⊢
    intro varL
    specialize lm4 (HUnionElemAt.pureAt _ _ .fst varL)
    dsimp [LeftTypeAt] at lm3
    replace lm3 := fun ec => lm3 ec varL
    rw [← (huVal.embedAt_injective_at .fst).eq_iff]
    calc
      _ = _ := lm3 ecL1
      _ = _ := congrArg _ lm4
      _ = _ := (lm3 ecL2).symm
  · dsimp [Function.Injective, embedAt_snd]
    intro ecL1 ecL2 lm4
    simp only [← DFunLike.coe_injective.eq_iff, funext_iff] at lm4 ⊢
    intro varL
    specialize lm4 (HUnionElemAt.pureAt _ _ .snd varL)
    dsimp [LeftTypeAt] at lm3
    replace lm3 := fun ec => lm3 ec varL
    rw [← (huVal.embedAt_injective_at .snd).eq_iff]
    calc
      _ = _ := lm3 ecL1
      _ = _ := congrArg _ lm4
      _ = _ := (lm3 ecL2).symm

theorem embedAt_injective_at (h: IsEmbeddable s) (lb: Label) : Function.Injective (s.embedAt lb) := h.embedAt_injective

def toEmbeddingAt (h: IsEmbeddable s) (lb: Label) : Function.Embedding (lb.casesOn EC1 EC2) ECR := ⟨s.embedAt lb, h.embedAt_injective_at lb⟩


end IsEmbeddable


structure Embeddable
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)]
  extends toStruct: EmbeddableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR where
  valid: IsEmbeddable toStruct

structure LiftableStruct
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)]
  extends toEmbeddable: EmbeddableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR where
  liftAt (lb: Label) (ecr: ECR) (req: ecr ∈ Set.range (toEmbeddable.embedAt lb)) : lb.casesOn EC1 EC2
  isInRangeAt (lb: Label) (ecr: ECR) : Bool

structure IsLiftable (s: LiftableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR) : Prop
  extends toEmbeddable: IsEmbeddable s.toEmbeddable where
  embedAt_liftAt_eq_self (lb: Label) (ec: lb.casesOn EC1 EC2) : s.liftAt lb (s.embedAt lb ec) (Set.mem_range_self _) = ec
  isInRangeAt_valid (lb: Label) (ecr: ECR) : (s.isInRangeAt lb ecr = .true) ↔ (ecr ∈ Set.range (s.embedAt lb))

namespace IsLiftable

variable {s: LiftableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR}

def toLiftableEmbeddingAt (h: IsLiftable s) (lb: Label) : LiftableEmbedding (lb.casesOn EC1 EC2) ECR where
  toEmbedding := h.toEmbeddingAt lb
  lift := s.liftAt lb
  lift_valid := h.embedAt_liftAt_eq_self lb

@[reducible]
def toHasHUnion (h: IsLiftable s) : HasHUnion EC1 EC2 where
  R := ECR
  fst := h.toLiftableEmbeddingAt .fst
  snd := h.toLiftableEmbeddingAt .snd

theorem toHasHUnion_embedRangeAt_eq_embedAt_range (h: IsLiftable s) {lb: Label}
  : @EmbedRangeAt EC1 EC2 (h.toHasHUnion) lb = Set.range (s.embedAt lb) := by
  cases lb <;> (dsimp [EmbedRangeAt]; congr)

@[reducible]
def toDecidableEmbedRange (h: IsLiftable s) : @HasHUnion.DecidableEmbedRange EC1 EC2 (h.toHasHUnion) :=
  fun lb ecr => decidable_of_iff (s.isInRangeAt lb ecr = .true) (by
    refine Iff.trans (h.isInRangeAt_valid lb ecr) ?_
    rw [← h.toHasHUnion_embedRangeAt_eq_embedAt_range])

@[reducible]
def toHasHUnionBundle (h: IsLiftable s) : HasHUnion.Bundle EC1 EC2 where
  hasHUnion := h.toHasHUnion
  memDecidable := h.toDecidableEmbedRange

end IsLiftable


structure Liftable
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)]
  extends toStruct: LiftableStruct EC1 EC2 Var1 Var2 Val1 Val2 ECR where
  valid: IsLiftable toStruct

end Interleaving


class HasInterleaving (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] where
  var: HasHUnion.Bundle.{uvar_l, uvar_r} Var1 Var2
  val: HasHUnion.Bundle.{uval_l, uval_r} Val1 Val2
  R: Type uec_r
  evalLikeR: EvalLike R (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)
  interleaving: Interleaving.Liftable EC1 EC2 Var1 Var2 Val1 Val2 R

attribute [reducible, instance] HasInterleaving.var HasInterleaving.val HasInterleaving.evalLikeR

namespace HasInterleaving

abbrev interleavingAt
  (EC1 EC2: Type uec_l) {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l}
  [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] [HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]
  : Interleaving.Liftable EC1 EC2 Var1 Var2 Val1 Val2 (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) :=
  HasInterleaving.interleaving

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]

@[defeq]
theorem interleavingAt_def : interleavingAt EC1 EC2 = interleaving := rfl

instance toHasHUnionBundle : HasHUnion.Bundle EC1 EC2 := HasInterleaving.interleaving.valid.toHasHUnionBundle

def merge (ec1: EC1) (ec2: EC2) : HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2 := HasInterleaving.interleaving.op ec1 ec2

@[defeq]
theorem merge_def {ec1: EC1} {ec2: EC2} : merge ec1 ec2 = interleaving.op ec1 ec2 := rfl

theorem merge_eq_interleaving_op : (merge: EC1 → EC2 → _) = interleaving.op := by
  simp only [funext_iff]
  intro _ _
  exact merge_def

theorem embedAt_eq_interleaving_embedAt : embedAt EC1 EC2 = interleaving.embedAt := by
  simp only [funext_iff]
  intro lb _
  cases lb <;> rfl

@[defeq]
theorem embedAt_fst_eq_merge {ec1: EC1} : embedAt EC1 EC2 .fst ec1 = merge ec1 ((interleavingAt EC1 EC2).emptyAt .snd) := rfl

@[defeq]
theorem embedAt_snd_eq_merge {ec2: EC2} : embedAt EC1 EC2 .snd ec2 = merge ((interleavingAt EC1 EC2).emptyAt .fst) ec2 := rfl

theorem liftAt_apply_fst_eq_snd_of_inter_mem_at
  (ecR: HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) {varR: HasHUnion.R Var1 Var2} (req: varR ∈ hinterSetUnivAt Var1 Var2)
  : ecR (HUnionElemAt.pureAt _ _ .fst (liftAt Var1 Var2 varR .fst (embedRangeAt_mem_of_hinterSetUnivAt_mem_at req .fst))) =
    ecR (HUnionElemAt.pureAt _ _ .snd (liftAt Var1 Var2 varR .snd (embedRangeAt_mem_of_hinterSetUnivAt_mem_at req .snd)))
  := by
  simp [HUnionElemAt.pureAt_eq_embedAt_mk, liftAt_embedAt_eq]

end HasInterleaving

end EvalLike


namespace StandardType

open EvalLike

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [hi: HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]

structure InterleavingStruct
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l)
  [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] [hi: HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2] where
  projectAt (lb: Label) (ecr: hi.R) : lb.casesOn EC1 EC2

namespace InterleavingStruct

theorem leftEvalAt_eq_projectAt {s: InterleavingStruct EC1 EC2 Var1 Var2 Val1 Val2} {ecR: hi.R} {lb: Label}
  : leftEvalAt (s.projectAt .fst ecR) (s.projectAt .snd ecR) lb = s.projectAt lb ecR := by
  rcases lb
  · dsimp [leftEvalAt_fst]
  · dsimp [leftEvalAt_snd]

end InterleavingStruct


structure IsInterleaving (s: InterleavingStruct EC1 EC2 Var1 Var2 Val1 Val2) : Prop where
  projectAt_eta (ecr: hi.R) : hi.merge (s.projectAt .fst ecr) (s.projectAt .snd ecr) = ecr

theorem isInterleaving_iff_forall₂ {s: InterleavingStruct EC1 EC2 Var1 Var2 Val1 Val2}
  : (IsInterleaving s) ↔ (∀(ecr: hi.R) (x : HUnionElemAt Var1 Var2), (hi.merge (s.projectAt .fst ecr) (s.projectAt .snd ecr)) x = ecr x) := by
  constructor
  · rintro ⟨lm1⟩ ecr x
    specialize lm1 ecr
    rw [lm1]
  · intro lm1
    refine .mk ?_
    intro ecr
    simp only [← EvalLike.coe_injective.eq_iff, ← DFunLike.coe_injective.eq_iff, funext_iff]
    exact lm1 ecr


structure Interleaving
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l)
  [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] [hi: HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]
  extends toStruct: InterleavingStruct EC1 EC2 Var1 Var2 Val1 Val2 where
  valid: IsInterleaving toStruct


def SetOfInterleavingValueDomainAt (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) (var: HUnionElemAt Var1 Var2) : Set (HUnionElemAt Val1 Val2) :=
  let s1 : Set Val1 := var.recLiftDiffAt .fst (fun x => sty1.dom x.liftAt) (fun _ => ∅)
  let s2 : Set Val2 := var.recLiftDiffAt .snd (fun x => sty2.dom x.liftAt) (fun _ => ∅)
  HUnionElemAt.setOfHUnion s1 s2

namespace IsInterleaving

variable {s: InterleavingStruct EC1 EC2 Var1 Var2 Val1 Val2}

/-
theorem projectAt_eta_iff (h: IsInterleaving s) (ecr: hi.R) (x : HUnionElemAt Var1 Var2)
  : (hi.interleaving.op (s.projectAt .fst ecr) (s.projectAt .snd ecr)) x = ecr x := by
-/
  --simp only [← EvalLike.coe_injective.eq_iff, ← DFunLike.coe_injective.eq_iff, funext_iff]

open HasInterleaving in
theorem projectAt_eq_self_of_diff_mem
  (h: IsInterleaving s) {ecR: hi.R} {varR: HasHUnion.R Var1 Var2} {lb: Label} (req: varR ∈ hdiffSetUnivAt Var1 Var2 lb)
  : embedAt _ _ lb ((s.projectAt lb ecR) (liftAt _ _ varR lb (embedRangeAt_mem_of_hdiffSetUnivAt_mem req))) = (ecR (HUnionElemAt.ofRightType varR (hunionSetUnivAt_mem_of_hdiffSetUnivAt_mem req))).val := by
  let il := interleavingAt EC1 EC2
  have lm1 : il.op = merge := rfl
  have lm4 := il.valid.interleave.diff
  specialize lm4 (s.projectAt .fst ecR) (s.projectAt .snd ecR) lb ⟨varR, req⟩
  cases lb <;> (
    dsimp [HDiffElemAt.lift, leftEvalAt] at lm4
    refine Eq.trans lm4 ?_
    rewrite [lm1, h.projectAt_eta]
    dsimp [HDiffElemAt.toUnion, HUnionElemAt.ofRightType] )

/-
open HasInterleaving in
theorem merge_eq_iff_projectAt_eq (h: IsInterleaving s) {ec1: EC1} {ec2: EC2} {ecR: hi.R}
  : (hi.merge ec1 ec2 = ecR) ↔ ((s.projectAt .fst ecR = ec1) ∧ (s.projectAt .snd ecR = ec2)) := by
  constructor
  · intro lm1
    have lm2 := h.projectAt_eta ecR
    simp only [← EvalLike.coe_injective.eq_iff, ← DFunLike.coe_injective.eq_iff, funext_iff] at ⊢ lm1 lm2
    let il := HasInterleaving.interleavingAt EC1 EC2
    rcases il.valid with ⟨⟨⟨lm3, lm4⟩, lm5⟩, lm6, lm7⟩
    clear lm6 lm7
    have lm6 : il.op = merge := merge_eq_interleaving_op.symm
    have lm7 : il.embedAt = embedAt EC1 EC2 := embedAt_eq_interleaving_embedAt.symm
    let huVar : HasHUnion Var1 Var2 := inferInstance
    refine ⟨?_, ?_⟩
    · intro var1
      specialize lm1 (HUnionElemAt.pureAt _ _ .fst var1)
      specialize lm2 (HUnionElemAt.pureAt _ _ .fst var1)
      dsimp [LeftTypeAt] at lm5
      replace lm5 := fun ec1 => lm5 .fst ec1 var1
      dsimp at lm5
      simp only [lm7] at lm5
      cases var1 using (huVar.recDiffInterAt .fst) <;> rename_i var1
      · replace lm3 := fun ec1 ec2 => lm3 ec1 ec2 .fst var1
        dsimp [leftEvalAt] at lm3
        rewrite [lm6] at lm3
        have lm8 := lm3 (s.projectAt .fst ecR) (s.projectAt .snd ecR)
-/
/-
      replace lm3 := lm3 ec1 (il.emptyAt .snd) .fst
      replace lm4 := fun ec1 => lm4 ec1 (il.emptyAt .snd)
      dsimp [leftEvalAt] at lm3
      simp only [lm7] at lm5
      simp only [lm6] at lm3 lm4
      rewrite [← embedAt_fst_eq_merge] at lm3
      cases var1 using (huVar.recDiffInterAt .fst) <;> rename_i var1
      · specialize lm3 var1
-/
      --simp [HUnionElemAt.pureAt_eq_embedAt_mk] at lm1 lm2
/-
    rewrite [Eq.comm] at lm1
    subst lm1
    refine ⟨?_, ?_⟩
    ·
-/



open HasInterleaving in
theorem projectAt_eq_exists_of_apply_eq (h: IsInterleaving s) {ecR: hi.R} {varR: HUnionElemAt Var1 Var2} {valR: HUnionElemAt Val1 Val2} (req: ecR varR = valR)
  : (∃(lb: Label), ∃(req1: varR.val ∈ EmbedRangeAt Var1 Var2 lb), ∃(req2: valR.val ∈ EmbedRangeAt Val1 Val2 lb), (s.projectAt lb ecR) (liftAt Var1 Var2 varR.val lb req1) = (liftAt Val1 Val2 valR.val lb req2))
  := by
  let il := HasInterleaving.interleavingAt EC1 EC2
--  intro lm1
  have lm2 := h.projectAt_eta ecR
  replace lm2 := lm2.symm ▸ req
  cases varR using HUnionElemAt.recDiffInter <;> rename_i varL
  · exists Label.fst
    have lm3 := il.valid.interleave.diff (s.projectAt .fst ecR) (s.projectAt .snd ecR) .fst varL
    rewrite [← merge_eq_interleaving_op, (h.projectAt_eta ecR)] at lm3
    dsimp [leftEvalAt_fst] at lm3
    refine ⟨?_, ?_, ?_⟩
    · dsimp [HDiffElemAt.toUnion]
      exact embedRangeAt_mem_of_hdiffSetUnivAt_mem varL.property
    · simp [EmbedRangeAt]
      exists ((s.projectAt Label.fst ecR) varL.lift)
      rewrite [Eq.comm] at req
      subst req
      exact lm3
    · rw [← (embedAt_injective_at .fst).eq_iff]
      simp [liftAt_embedAt_eq]
      rewrite [Eq.comm] at req
      subst req
      refine Eq.trans ?_ lm3
      rw [(embedAt_injective_at .fst).eq_iff]
      refine congrArg _ ?_
      dsimp [HDiffElemAt.lift, HDiffElemAt.toUnion]
  · exists Label.snd
    have lm3 := il.valid.interleave.diff (s.projectAt .fst ecR) (s.projectAt .snd ecR) .snd varL
    rewrite [← merge_eq_interleaving_op, (h.projectAt_eta ecR)] at lm3
    dsimp [leftEvalAt_fst] at lm3
    refine ⟨?_, ?_, ?_⟩
    · dsimp [HDiffElemAt.toUnion]
      exact embedRangeAt_mem_of_hdiffSetUnivAt_mem varL.property
    · simp [EmbedRangeAt]
      exists ((s.projectAt Label.snd ecR) varL.lift)
      rewrite [Eq.comm] at req
      subst req
      exact lm3
    · rw [← (embedAt_injective_at .snd).eq_iff]
      simp [liftAt_embedAt_eq]
      rewrite [Eq.comm] at req
      subst req
      refine Eq.trans ?_ lm3
      rw [(embedAt_injective_at .snd).eq_iff]
      refine congrArg _ ?_
      dsimp [HDiffElemAt.lift, HDiffElemAt.toUnion]
  · have lm3 := il.valid.interleave.inter (s.projectAt .fst ecR) (s.projectAt .snd ecR) varL
    rewrite [← merge_eq_interleaving_op, (h.projectAt_eta ecR)] at lm3
    obtain ⟨lb, lm3⟩ := lm3
    exists lb
    have lm4 := hinterSetUnivAt_mem_iff_embedRangeAt_mem.mp varL.property lb
    refine ⟨?_, ?_, ?_⟩
    · dsimp [HInterElemAt.toUnion]
      exact lm4
    · simp [EmbedRangeAt]
      rewrite [Eq.comm] at req
      subst req
      exact Exists.intro _ lm3
    · rw [← (embedAt_injective_at lb).eq_iff]
      simp [liftAt_embedAt_eq]
      rewrite [Eq.comm] at req
      subst req
      refine Eq.trans ?_ lm3
      rw [(embedAt_injective_at lb).eq_iff]
      dsimp [HInterElemAt.liftAt, HInterElemAt.toUnion]
      rcases lb
      · dsimp [leftEvalAt_fst]
      · dsimp [leftEvalAt_snd]
/-
  · rintro ⟨lb, req, lm2, lm3⟩
    rcases varR with ⟨varR, lm4⟩
    rcases valR with ⟨valR, lm5⟩
    dsimp at lm1 lm2 lm3
    have lm_s : lm4 = hunionSetUnivAt_mem_of_embedRangeAt_mem lm1 := rfl
    subst lm_s
    have lm_s : lm5 = hunionSetUnivAt_mem_of_embedRangeAt_mem lm2 := rfl
    subst lm_s
    have lm4 := lm3.symm
    rewrite [← (embedAt_eq_iff_liftAt_eq lm2)] at lm4
    have lm1_1 := lm1
    have lm2_1 := lm2
    simp [EmbedRangeAt] at lm1_1 lm2_1
    obtain ⟨varL, lm5⟩ := lm1_1
    obtain ⟨valL, lm6⟩ := lm2_1
    rcases il.valid.interleave with ⟨lm7, lm8⟩
    by_cases lm9: varR ∈ EmbedRangeAt Var1 Var2 lb.toDual
    · have lm10 (lb0: Label) : varR ∈ EmbedRangeAt Var1 Var2 lb0 := by
        by_cases lm10_1: lb = lb0
        · subst lm10_1
          exact lm1
        · simp [Label.ne_iff_eq_toDual_symm] at lm10_1
          subst lm10_1
          exact lm9
      have lm11 := hinterSetUnivAt_mem_iff_embedRangeAt_mem.mpr lm10
      simp [Subtype.ext_iff]
      specialize lm8 (s.projectAt .fst ecR) (s.projectAt .snd ecR) ⟨varR, lm11⟩
      rewrite [← merge_eq_interleaving_op, h.projectAt_eta ecR] at lm8
      simp only [s.leftEvalAt_eq_projectAt] at lm8
      rcases lm8 with ⟨lb2, lm8⟩
      dsimp [HInterElemAt.toUnion, HInterElemAt.liftAt] at lm8
      rw [← lm8, ← lm4]
      by_cases lm12: lb = lb2
      · subst lm12
        rfl
      · simp [Label.ne_iff_eq_toDual_symm] at lm12
        subst lm12
        symm
        refine @AreEquiv.embedAt_eq_toDual Val1 Val2 _ (fun lb0 => (s.projectAt lb0 ecR) (liftAt Var1 Var2 varR lb0 (lm10 lb0))) lb ?_
        intro lb2
        rcases lb2
        · simp [AreEquivAt.fst_iff, LeftTypeAt]
-/
/-
        have lm5_1 := (embedAt_eq_iff_liftAt_eq lm1).mp lm5
        have lm12 := lm9
        simp [EmbedRangeAt] at lm12
        obtain ⟨valLD, lm12⟩ := lm12
        have lm12_1 := (embedAt_eq_iff_liftAt_eq lm9).mp lm12
-/

        --refine @AreEquiv.embedAt_eq_toDual Val1 Val2 _ (fun lb0 => (s.projectAt lb0 ecR) (liftAt Var1 Var2 varR lb0 (lm10 lb0))) lb ?_
        --intro lb2
        --rewrite [AreEquivAt.toDual_iff]
        --simp [lm5_1, lm12_1]
        --
        --symm
/-

        intro lb2
        rewrite [AreEquivAt.toDual_iff]
        dsimp [LeftTypeAt]
-/
        --simp only [← leftEvalAt_def]
        --dsimp [LeftTypeAt]
/-
        rcases lb
        · dsimp [Label.toDual] at ⊢ lm8 lm9
          symm
          refine AreEquiv.embedAt_fst_eq_snd ?_
          refine .mk ?_
          intro lb
          rcases lb
          · rw [AreEquivAt.fst_iff]
            simp [lm4]
          --rw [AreEquivAt.toDual_iff]
-/

/-
    rewrite [← (embedAt_injective_at lb).eq_iff] at lm3
    simp [liftAt_embedAt_eq] at lm3
    obtain ⟨lm4, lm5⟩ := il.valid.interleave
    specialize lm4 (s.projectAt .fst ecR) (s.projectAt .snd ecR) lb
    let huVar : HasHUnion Var1 Var2 := inferInstance
    cases lm6: liftAt Var1 Var2 varL.val lb lm1 using huVar.recDiffInterAt lb <;> rename_i x
    · clear lm5
      specialize lm4 x
      rewrite [← merge_eq_interleaving_op, (h.projectAt_eta ecR)] at lm4
      simp [HDiffElemAt.lift, liftAt_eq_liftAtAlt, liftAtAlt_injective.eq_iff] at lm6
      dsimp [HDiffElemAt.toUnion] at lm4
      simp [← lm6] at lm4
      rw [Subtype.ext_iff, ← lm3, ← lm4, embedAt_injective.eq_iff]
      simp only [lm6]
      dsimp [HDiffElemAt.lift]
      rcases lb
      · dsimp [leftEvalAt_fst]
      · dsimp [leftEvalAt_snd]
    · clear lm4
      simp [HInterElemAt.liftAt, liftAt_eq_liftAtAlt, liftAtAlt_injective.eq_iff] at lm6
      rcases varL with ⟨varL, lm7⟩
      rcases x with ⟨x, lm8⟩
      simp at lm6
      subst lm6
      rcases valL with ⟨valL, lm9⟩
      dsimp at lm1 lm2 lm3
      have lm_s : lm7 = hunionSetUnivAt_mem_of_hinterSetUnivAt_mem lm8 := rfl
      subst lm_s
      have lm_s : lm1 = embedRangeAt_mem_of_hinterSetUnivAt_mem_at lm8 lb := rfl
      subst lm_s
      have lm_s : lm9 = hunionSetUnivAt_mem_of_embedRangeAt_mem lm2 := rfl
      subst lm_s
      rewrite [← merge_eq_interleaving_op] at lm5
      rewrite [embedAt_eq_iff_liftAt_eq lm2] at lm3
      have lm7 := lm5 (s.projectAt .fst ecR) (s.projectAt .snd ecR) ⟨varL, lm8⟩
      rewrite [h.projectAt_eta ecR] at lm7
      dsimp [HInterElemAt.toUnion] at lm7
      rcases lm7 with ⟨lb, lm7⟩
      --simp only [embedAt_eq_iff_exists_liftAt_eq] at lm7
-/
/-
      replace lm5 := fun ec1 ec2 => lm5 ec1 ec2 ⟨varL, lm8⟩
      obtain ⟨lb, lm6⟩ := lm5 (il.emptyAt .fst) (il.emptyAt .snd)
      have lm6_1 := lm6
      rewrite [← HasInterleaving.embedAt_fst_eq_merge] at lm6_1
      have lm6_2 := lm6
      rewrite [← HasInterleaving.embedAt_snd_eq_merge] at lm6_2
      have lm7 := lm6_1.symm.trans lm6_2
      clear lm6_1 lm6_2
      dsimp [HInterElemAt.toUnion] at lm7
-/
/-
      rcases lb
      · dsimp [leftEvalAt_fst] at lm6
        rewrite [← HasInterleaving.embedAt_snd_eq_merge] at lm6
-/
      --have lm4 := lm5 ⟨varL, lm8⟩


/-
      specialize lm5 x
      rewrite [← merge_eq_interleaving_op, (h.projectAt_eta ecR)] at lm5
      simp [HInterElemAt.liftAt, liftAt_eq_liftAtAlt, liftAtAlt_injective.eq_iff] at lm6
      obtain ⟨lb2, lm5⟩ := lm5
      dsimp [HInterElemAt.toUnion] at lm5
      simp [← lm6] at lm5
      simp [EmbedRangeAt] at lm2
      obtain ⟨varL2, lm2⟩ := lm2
      rw [Subtype.ext_iff, ← lm5, ← lm2]
-/
/-
      by_cases lm7: lb = lb2
      · subst lm7
        rw [lm2, ← lm3, embedAt_injective.eq_iff]
        dsimp [HInterElemAt.liftAt]
        simp only [← lm6]
        rcases lb
        · dsimp [leftEvalAt_fst]
        · dsimp [leftEvalAt_snd]
      · simp [Label.ne_iff_eq_toDual] at lm7
        replace lm7 := Label.eq_toDual_symm lm7
        subst lm7
        rcases lb
        · dsimp [Label.toDual, leftEvalAt_snd]
          symm
          rw [embedAt_fst_eq_snd_iff_areEquiv_exists]
          exists valL
          refine .mk ?_ ?_ ?_
          · intro lb
            simp [EmbedRangeAt]
            dsimp [Label.toDual, leftEvalAt_snd] at lm5
            rcases lb
            · exact Exists.intro _ lm2
            · exists ((s.projectAt Label.snd ecR) (x.liftAt Label.snd))
-/
/-
        have lm7 := hinterSetUnivAt_mem_iff_toDual_embedRangeAt_mem.mp x.property lb
        revert lm1 lm7
        simp [EmbedRangeAt]
        intro x1 lm7 lm8 x2 lm9
        have lm10 := il.valid.embed_eq lb.toDual (s.projectAt lb.toDual ecR) x2
        have lm11 := il.valid.embed_eq lb (s.projectAt lb ecR) x1
        rewrite [← HasInterleaving.embedAt_eq_interleaving_embedAt] at lm10 lm11
        rcases lb
        · dsimp [Label.toDual, leftEvalAt_snd]
          dsimp [Label.toDual] at lm9 lm10
          simp [HUnionElemAt.pureAt_eq_embedAt_mk] at lm10 lm11
-/
        --simp [EmbedRangeAt] at lm7 lm1
/-
        obtain ⟨varL3, lm7⟩ := lm7
        rw [lm2]
        rewrite [← lm2, embedAt_injective.eq_iff] at lm3
-/
/-
    revert lm1 lm2
    simp [EmbedRangeAt]
    intro varL2 lm3 valL2 lm4 lm5
    simp [← lm3, embedAt_liftAt_eq] at lm5
-/
    --have lm3 := h.projectAt_eta ecR



theorem apply_inter_mem_of_inter_mem
  (h: IsInterleaving s) {ecR: hi.R} {varR: HasHUnion.R Var1 Var2} (req: varR ∈ hinterSetUnivAt Var1 Var2)
  : (ecR (HUnionElemAt.ofRightType varR (hunionSetUnivAt_mem_of_hinterSetUnivAt_mem req))).val ∈ hinterSetUnivAt Val1 Val2 := by
  dsimp [HUnionElemAt.ofRightType]
  rw [hinterSetUnivAt_mem_iff_embedRangeAt_mem]
  intro lb1
  let il := HasInterleaving.interleavingAt EC1 EC2
  obtain ⟨lb2, lm2⟩ := il.valid.interleave.inter (s.projectAt .fst ecR) (s.projectAt .snd ecR) ⟨varR, req⟩
  rewrite [← HasInterleaving.merge_eq_interleaving_op, h.projectAt_eta] at lm2
  dsimp [HInterElemAt.toUnion] at lm2
  by_cases lm3: lb1 = lb2
  · subst lm3
    rw [← lm2]
    simp only [EmbedRangeAt, Set.mem_range, exists_apply_eq_apply]
  · simp [Label.ne_iff_eq_toDual] at lm3
    subst lm3
    simp [EmbedRangeAt]
    have lm4 := il.valid.embed_eq
    have lm5 := hinterSetUnivAt_mem_iff_toDual_embedRangeAt_mem.mp req lb2
    simp [EmbedRangeAt] at lm5
    obtain ⟨varLD, lm5⟩ := lm5
    have lm6 := lm4 lb2.toDual (s.projectAt lb2.toDual ecR) varLD
    rewrite [← HasInterleaving.embedAt_eq_interleaving_embedAt] at lm6
    exists ((s.projectAt lb2.toDual ecR) varLD)
/-
  have lm4 := req
  revert req
  simp [hinterSetUnivAt_mem_iff_embedRangeAt_mem, EmbedRangeAt]
  intro req lb
  obtain ⟨varL, lm1⟩ := req lb
  obtain ⟨varLD, lm1_d⟩ := req lb.toDual
  let (eq := lm2) valR : HasHUnion.R Val1 Val2 := ecR (HUnionElemAt.pureAt _ _ lb varL)
  let (eq := lm2_d) valRD : HasHUnion.R Val1 Val2 := ecR (HUnionElemAt.pureAt _ _ lb.toDual varLD)
  simp [HUnionElemAt.pureAt_eq_embedAt_mk] at lm2 lm2_d
-/


  --let () valRD : HasHUnion.R Val1 Val2 := ecR (HUnionElemAt.pureAt _ _ lb.toDual varLD)
  --let valL : LeftTypeAt Val1 Val2 lb := ecR (HUni)
  --have lm2 := req lb

  --rewrite [hinterSetUnivAt_mem_iff_embedRangeAt_mem] at req

/-
open HasInterleaving in
theorem projectAt_fst_eq_snd_of_inter_mem
  (h: IsInterleaving s) {ecR: hi.R} {varR: HasHUnion.R Var1 Var2} (req: varR ∈ hinterSetUnivAt Var1 Var2)
  : embedAt Val1 Val2 .fst ((s.projectAt .fst ecR) (liftAt Var1 Var2 varR .fst (embedRangeAt_mem_of_hinterSetUnivAt_mem_at req .fst))) =
    embedAt Val1 Val2 .snd ((s.projectAt .snd ecR) (liftAt Var1 Var2 varR .snd (embedRangeAt_mem_of_hinterSetUnivAt_mem_at req .snd)))
  := by
  rw [HasHUnion.embedAt_fst_eq_snd_iff_areEquiv_exists]
  let valR := ecR (HUnionElemAt.ofRightType varR (hunionSetUnivAt_mem_of_hinterSetUnivAt_mem req))
  exists valR
  refine .mk ?_ ?_ ?_
  · have lm1 := valR.property
    rewrite [hunionSetUnivAt_mem_iff_embedRangeAt_mem] at lm1
    have lm4 := hinterSetUnivAt_mem_iff_embedRangeAt_mem.mp req
    subst valR
    dsimp [HUnionElemAt.ofRightType] at ⊢ lm1
    obtain ⟨lb1, lm1⟩ := lm1
    intro lb2
    by_cases lm2: lb1 = lb2
    · subst lm2
      exact lm1
    · simp [Label.ne_iff_eq_toDual] at lm2
      replace lm2 := Label.eq_toDual_symm lm2
      subst lm2
      have lm5 := lm4 lb1.toDual
      simp [EmbedRangeAt] at lm1 ⊢
      obtain ⟨valL, lm1⟩ := lm1
      let valLDual : LeftTypeAt Val1 Val2 lb1.toDual := liftAt Val1 Val2 (embedAt _ _ lb1 valL) lb1.toDual
      --simp [EmbedRangeAt] at lm1 ⊢
-/
/-
      obtain ⟨valL, lm1⟩ := lm1
      have lm3 := HasInterleaving.liftAt_apply_fst_eq_snd_of_inter_mem_at ecR req
      simp only [← lm1]
      let sdfsdf : LeftTypeAt Val1 Val2 lb2 := liftAt Val1 Val2 (embedAt _ _ lb1 valL) lb2
-/
/-
      cases lb1 <;> cases lb2 <;> simp at lm2
      · simp only [Eq.comm]
        simp only [HasHUnion.embedAt_fst_eq_snd_iff_areEquiv_exists]
        dsimp [LeftTypeAt] at ⊢ valL
-/
      --simp [HUnionElemAt.pureAt_eq_embedAt_mk, Subtype.ext_iff] at lm3
/-
      have lm3_1 := lm3
      conv at lm3_1 =>
        lhs
        simp [HUnionElemAt.pureAt_eq_embedAt_mk, liftAt_embedAt_eq]
      have lm3_2 := lm3
      conv at lm3_2 =>
        rhs
        simp [HUnionElemAt.pureAt_eq_embedAt_mk, liftAt_embedAt_eq]
      cases lb1 <;> cases lb2 <;> simp at lm2
      · simp [EmbedRangeAt] at lm1 ⊢
        obtain ⟨valL, lm1⟩ := lm1
        let varLDual : Val2 := (s.projectAt .snd ecR) (liftAt Var1 Var2 varR .snd (lm4 .snd))
        exists varLDual
        subst varLDual
        rw [← lm1]
        symm
        rw [HasHUnion.embedAt_fst_eq_snd_iff_areEquiv_exists]
-/
        --simp only [← lm1]
        --simp only [Eq.comm]


        --exists (liftAt Var1 Var2 varR Label.snd (lm4 .snd))
/-
        conv at lm3 =>
          rw [Subtype.ext_iff]
          lhs
          simp [HUnionElemAt.pureAt_eq_embedAt_mk, liftAt_embedAt_eq]
-/




        --have lm4 := liftAlt_dom_congr lm1 EmbedRangeAt.mem_self
        --rewrite [← liftAtAlt_injective.eq_iff] at lm4
        --simp [← liftAt_eq_liftAtAlt, embedAt_liftAt_eq] at lm4
        --rewrite []
    --have lm2 := HasInterleaving.liftAt_apply_fst_eq_snd_of_inter_mem_at ecR req
    --dsimp [HUnionElemAt.pureAt_eq_embedAt_mk] at lm2

    --simp only [liftAt_embedAt_eq] at lm2
    --subst valR
    --have lm1 := HasInterleaving.liftAt_apply_fst_eq_snd_of_inter_mem_at ecR req
  --have lm1 := HasInterleaving.liftAt_apply_fst_eq_snd_of_inter_mem_at ecR req
/-
  simp [HUnionElemAt.pureAt_eq_embedAt_mk] at lm1
  let il := interleavingAt EC1 EC2
  have lm2 : il.op = merge := merge_eq_interleaving_op.symm
  have lm3 : il.embedAt = embedAt EC1 EC2 := embedAt_eq_interleaving_embedAt.symm
-/
  --have lm1 := req
/-
  revert req
  simp only [hinterSetUnivAt_mem_iff_embedRangeAt_mem, EmbedRangeAt, Set.mem_range]
  intro req
  obtain ⟨varL1, lm1_1⟩ := req .fst
  obtain ⟨varL2, lm1_2⟩ := req .snd
  conv =>
    conv => lhs; arg 4; arg 2; simp only [← lm1_1]; rw [embedAt_liftAt_eq]
    conv => rhs; arg 4; arg 2; simp only [← lm1_2]; rw [embedAt_liftAt_eq]
  let il := interleavingAt EC1 EC2
  have lm2 : il.op = merge := merge_eq_interleaving_op.symm
  have lm5 : il.embedAt = embedAt EC1 EC2 := embedAt_eq_interleaving_embedAt.symm
  obtain ⟨lb, lm3⟩ := il.valid.interleave.inter (s.projectAt .fst ecR) (s.projectAt .snd ecR) ⟨varR, lm1⟩
  rewrite [lm2, h.projectAt_eta] at lm3
  have lm4_1 := il.valid.embed_eq .fst (s.projectAt .fst ecR) varL1
  have lm4_2 := il.valid.embed_eq .snd (s.projectAt .snd ecR) varL2
  rewrite [lm5] at lm4_1 lm4_2
  dsimp [HUnionElemAt.pureAt, HUnionElemAt.ofEmbedElem, EmbedElemAt.pureAt] at lm4_1 lm4_2
  conv at lm4_1 => rhs; arg 1; arg 2; arg 1; simp only [lm1_1, ← lm1_2]
  conv at lm4_2 => rhs; arg 1; arg 2; arg 1; simp only [lm1_2, ← lm1_1]
  have lm6_1 := liftAlt_dom_congr lm1_1 (EmbedRangeAt.mem_self)
  have lm6_2 := liftAlt_dom_congr lm1_2 (EmbedRangeAt.mem_self)
  rewrite [← liftAtAlt_injective.eq_iff] at lm6_1 lm6_2
  dsimp [← liftAt_eq_liftAtAlt] at lm6_1 lm6_2
  rewrite [embedAt_liftAt_eq] at  lm6_1
  have lm8 := HasInterleaving.liftAt_apply_fst_eq_snd_of_inter_mem_at ecR lm1
  cases lb
  · dsimp [leftEvalAt_fst] at lm3
    simp only [← lm1_1] at lm3
    dsimp [HInterElemAt.liftAt, HInterElemAt.toUnion] at lm3
    rewrite [embedAt_liftAt_eq] at lm3
    have lm7 := lm3.symm.trans lm4_1
-/


  --obtain ⟨var2, lm2_2⟩ := lm1 .snd
  --have lm2 := h.projectAt_eta ecR

/-
theorem eq_iff_of_inter_mem
  (h: IsInterleaving s) {ecR: hi.R} {varR: HasHUnion.R Var1 Var2} {valR: HasHUnion.R Val1 Val2} (req: varR ∈ hinterSetUnivAt Var1 Var2)
  : ((ecR (HUnionElemAt.ofRightType varR (hunionSetUnivAt_mem_of_hinterSetUnivAt_mem req))).val = valR) ↔
    (∃(lb: Label), embedAt Val1 Val2 lb ((s.projectAt lb ecR) (liftAt Var1 Var2 varR lb (embedRangeAt_mem_of_hinterSetUnivAt_mem_at req lb))) = valR)
  := by
-/


/-
def interleave (h: IsInterleaving s) (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) : StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2) where
  dom := SetOfInterleavingValueDomainAt sty1 sty2
  valid ecr var := by
    have lm1 := sty1.valid
    have lm2 := sty2.valid
    let il := HasInterleaving.interleavingAt EC1 EC2
    rcases il with ⟨il, lm3⟩
    let ec1 := (s.projectAt .fst ecr)
    let ec2 := (s.projectAt .snd ecr)
    dsimp at ec1 ec2
    specialize lm1 ec1
    specialize lm2 ec2
    cases var using HUnionElemAt.recDiffInter <;> rename_i x
    · let x1 := x.lift
      dsimp [LeftTypeAt] at x1
      have lm4 := x.property
      rewrite [hdiffSetUnivAt_mem_iff_embedRangAt_mem] at lm4
      simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
      refine Or.inl ?_
      exists (ec1 x1)
      refine ⟨?_, ?_⟩
      · dsimp [HUnionElemAt.recLiftDiffAt, HDiffElemAt.toUnion]
        simp [DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, lm4]
        specialize lm1 x1
        subst x1
        exact lm1
      · rw [Subtype.ext_iff, HUnionElemAt.pureAt_val_eq_embedAt]
        dsimp [HDiffElemAt.toUnion]
        subst x1
        subst ec1
        exact h.projectAt_eq_self_of_diff_mem x.property
-/


end IsInterleaving

/-
def interleave (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) : StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2) where
  dom := SetOfInterleavingValueDomainAt sty1 sty2
  valid ec var := by
    have lm1 := sty1.valid
    have lm2 := sty2.valid
    let il := HasInterleaving.interleavingAt EC1 EC2 Var1 Var2 Val1 Val2
    rcases il with ⟨il, lm3⟩
    cases ec using (IsInterleavingLike.recRightEval lm3)
    rename_i ec1 ec2
    specialize lm1 ec1
    specialize lm2 ec2
    rcases lm3 with ⟨⟨lm3, lm4⟩, lm5, lm6⟩
    specialize lm3 ec1 ec2
    specialize lm4 ec1 ec2
    cases var using HUnionElemAt.recDiffInter <;> rename_i x
    · specialize lm3 .fst x
      specialize lm1 x.lift
      simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
      refine Or.inl ?_
      exists ((ec1: Eval Var1 Val1) x.lift)
      refine ⟨?_, ?_⟩
      · have lm7 := x.property
        rewrite [hdiffSetUnivAt_mem_iff_embedRangAt_mem] at lm7
        dsimp [HUnionElemAt.recLiftDiffAt, HDiffElemAt.toUnion, EmbedElemAt.liftAt]
        simp [DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, lm7]
        exact lm1
      · rw [Subtype.ext_iff, HUnionElemAt.pureAt_val_eq_embedAt]
        exact lm3
    · specialize lm3 .snd x
      specialize lm2 x.lift
      simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
      refine Or.inr ?_
      exists ((ec2: Eval Var2 Val2) x.lift)
      refine ⟨?_, ?_⟩
      · have lm7 := x.property
        rewrite [hdiffSetUnivAt_mem_iff_embedRangAt_mem] at lm7
        dsimp [HUnionElemAt.recLiftDiffAt, HDiffElemAt.toUnion, EmbedElemAt.liftAt]
        simp [DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, lm7]
        exact lm2
      · rw [Subtype.ext_iff, HUnionElemAt.pureAt_val_eq_embedAt]
        exact lm3
    · specialize lm4 x
      specialize lm1 (x.liftAt .fst)
      specialize lm2 (x.liftAt .snd)
      rcases lm4 with ⟨lb, lm4⟩
      simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion, Subtype.ext_iff, HUnionElemAt.pureAt_val_eq_embedAt, ← lm4]
      have lm7 := x.property
      rewrite [hinterSetUnivAt_mem_iff_embedRangeAt_mem] at lm7
      cases lb
      · refine Or.inl ?_
        simp [HUnionElemAt.recLiftDiffAt, DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, HInterElemAt.toUnion, lm7]
        exists ((ec1: Eval Var1 Val1) (x.liftAt .fst))
      · refine Or.inr ?_
        simp [HUnionElemAt.recLiftDiffAt, DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, HInterElemAt.toUnion, lm7]
        exists ((ec2: Eval Var2 Val2) (x.liftAt .snd))
-/

def invInterleaveAt
  (x: StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)) (lb: Label)
  : StandardType (lb.casesOn EC1 EC2) (LeftTypeAt Var1 Var2 lb) (LeftTypeAt Val1 Val2 lb) where
  dom var := x.dom (.pureAt _ _ lb var) |> (HUnionElemAt.liftSetAt · lb)
  valid := by
    let il : Interleaving EC1 EC2 Var1 Var2 Val1 Val2 _ := HasInterleaving.interleaving
    rcases il with ⟨op, lm1⟩
    rcases lm1 with ⟨⟨lm1, lm2⟩, lm3, lm4⟩
    have lm5 := x.valid
    cases lb
    · dsimp [LeftTypeAt]
      intro ec1 lv1
      simp [HUnionElemAt.liftSetAt]
      obtain ⟨ec2⟩ := lm3.mp ⟨ec1⟩
      specialize lm5 (op ec1 ec2) (HUnionElemAt.pureAt _ _ .fst lv1)
      refine Eq.subst ?_ lm5
      refine Subtype.ext ?_
      rw [HUnionElemAt.pureAt_val_eq_embedAt]
-/

/-
def invInterleaveAt
  (x: StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)) (lb: Label) [Nonempty (lb.casesOn EC2 EC1)]
  : StandardType (lb.casesOn EC1 EC2) (LeftTypeAt Var1 Var2 lb) (LeftTypeAt Val1 Val2 lb) where
  dom var := x.dom (.pureAt _ _ lb var) |> (HUnionElemAt.liftSetAt · lb)
  valid := by
    rename_i req
    let ⟨opR, lm1, lm2⟩ : Interleaving Var1 Var2 Val1 Val2 EC1 EC2 _ := HasInterleaving.interleaving
    rcases x with ⟨domR, lm3⟩
    --have lm4 := Nonempty.intro opR
    --simp at lm4
    cases lb
    · dsimp [LeftTypeAt, HUnionElemAt.pureAt, EmbedElemAt.pureAt, HUnionElemAt.ofEmbedElem, HUnionElemAt.liftSetAt]
      dsimp at req
      obtain ⟨ec2⟩ := req
      intro ec1 lv
      let ecr := opR ec1 ec2
      specialize lm3 ecr (.pureAt _ _ .fst lv)
      subst ecr
      simp [HUnionElemAt.pureAt, EmbedElemAt.pureAt, HUnionElemAt.ofEmbedElem] at lm3
      rcases lm1 with ⟨lm1_1, lm1_2, lm1_3⟩
-/

/-

    cases lb
-/
/-
    · dsimp [LeftTypeAt, HUnionElemAt.pureAt, EmbedElemAt.pureAt, HUnionElemAt.ofEmbedElem, HUnionElemAt.liftSetAt]
      intro ec lv
-/
/-
theorem interleave_uncurry_surjective : Function.Surjective (Function.uncurry (interleave: StandardType EC1 Var1 Val1 → StandardType EC2 Var2 Val2 → StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2))) := by
  rintro ⟨domr, lm1⟩
  simp [interleave]
  simp only [funext_iff]
  let sty1 : StandardType EC1 Var1 Val1 := .mk
-/

/-
namespace IsSafe

def interleave (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2)

--structure Interleaving (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2)


end IsSafe
-/

/-
theorem interleave_isSafe_iff
  {sty1: StandardType EC1 Var1 Val1} {sty2: StandardType EC2 Var2 Val2}
  {v: HUnionElemAt Var1 Var2} {d: Set (HUnionElemAt Val1 Val2)}
  : ((interleave sty1 sty2).IsSafe v d) ↔
    ((∃req, sty1.IsSafe (v.liftAt .fst req) (HUnionElemAt.liftSetAt d .fst)) ∨ (∃req, sty2.IsSafe (v.liftAt .snd req) (HUnionElemAt.liftSetAt d .snd)))
  := by
  cases v using HUnionElemAt.recDiffInter <;> rename_i x
  · dsimp [HDiffElemAt.toEmbedElem, HUnionElemAt.ofEmbedElem, HUnionElemAt.liftAt,
           HUnionElemAt.liftSetAt, HUnionElemAt.pureAt, EmbedElemAt.pureAt, interleave]
    simp [isSafe_iff]
    have lm2 := x.property |> hdiffSetUnivAt_mem_iff_embedRangAt_mem.mp
    simp [lm2]
    conv =>
      lhs; ext; ext; ext
      simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion, HUnionElemAt.recLiftDiffAt, DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, lm2]
      simp [EmbedElemAt.liftAt, HUnionElemAt.pureAt, EmbedElemAt.pureAt, HUnionElemAt.ofEmbedElem]
    constructor
    · intro lm1 lv lm3
      have lm4 := lm1 (embedAt _ _ .fst lv) embedAt_hunionSetUnivAt_mem lm3
      rcases lm4 with ⟨lv2, lm4, lm5⟩
      rewrite [(embedAt_injective _ _).eq_iff] at lm5
      subst lm5
      exact lm4
    · intro lm1 rv lm3 lm4
      by_contra lm5
      simp at lm5
-/
      --let x1 := liftAt _ _ x.val .fst lm2.left
      --dsimp [LeftTypeAt] at x1

/-
    constructor
    · intro lm1
      refine Or.inl ?_
      refine ⟨?_, ?_⟩
      · exact embedRangeAt_mem_of_hdiffSetUnivAt_mem x.property
      · intro lv lm2
        specialize lm1 (embedAt _ _ .fst lv) embedAt_hunionSetUnivAt_mem lm2
        simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion, HUnionElemAt.recLiftDiffAt, DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff] at lm1
        have lm3 := x.property |> hdiffSetUnivAt_mem_iff_embedRangAt_mem.mp
        simp [lm3] at lm1
        rcases lm1 with ⟨x2, lm1⟩
-/
      --simp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion] at lm1
/-
  simp only [isSafe_iff]
  dsimp [interleave, SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
  simp [- Subtype.forall]
-/
  --: (∀v d, (interleave sty1 sty2).IsSafe v d) ↔ ((∀v d, sty1.IsSafe v d) ∧ (∀v d, sty2.IsSafe v d)) := by


end StandardType


end Nemonuri.ProgramGraph

end
