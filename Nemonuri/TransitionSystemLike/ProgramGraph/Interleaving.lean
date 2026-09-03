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

end LeftEvalAt

structure IsInterleaving
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2]
  (op: EC1 → EC2 → (HUnionElemAt Var1 Var2) → (HUnionElemAt Val1 Val2)) : Prop where
  diff (ec1: EC1) (ec2: EC2) (lb: Label) (x: HDiffElemAt Var1 Var2 lb) :
    embedAt Val1 Val2 lb ((leftEvalAt ec1 ec2 lb: Eval (LeftTypeAt Var1 Var2 lb) (LeftTypeAt Val1 Val2 lb)) x.lift) = (op ec1 ec2 (x.toUnion)).val
  inter (ec1: EC1) (ec2: EC2) (x: HInterElemAt Var1 Var2) :
    ∃(lb: Label), embedAt Val1 Val2 lb ((leftEvalAt ec1 ec2 lb: Eval (LeftTypeAt Var1 Var2 lb) (LeftTypeAt Val1 Val2 lb)) (x.liftAt lb)) = (op ec1 ec2 (x.toUnion)).val

--#print IsInterleaving
/-
  diff_fst (x: HDiffElemAt Var1 Var2 .fst) (ec1: EC1) (ec2: EC2) :
    embedAt Val1 Val2 .fst ((ec1: Eval Var1 Val1) x.lift) = (op ec1 ec2 (x.toUnion)).val
  diff_snd (x: HDiffElemAt Var1 Var2 .snd) (ec1: EC1) (ec2: EC2) :
    embedAt Val1 Val2 .snd ((ec2: Eval Var2 Val2) x.lift) = (op ec1 ec2 (x.toUnion)).val
  inter (x: HInterElemAt Var1 Var2) (ec1: EC1) (ec2: EC2) :
    (embedAt Val1 Val2 .fst ((ec1: Eval Var1 Val1) (x.liftAt .fst)) = (op ec1 ec2 (x.toUnion)).val) ∨
    (embedAt Val1 Val2 .snd ((ec2: Eval Var2 Val2) (x.liftAt .snd)) = (op ec1 ec2 (x.toUnion)).val)
-/
    --let rhs := op ec1 ec2 (x.toUnion)

    --(.ofEmbedElem (EmbedElemAt.mapAt Var1 Var2 Val1 Val2 .snd (ec2: Eval Var2 Val2) (x.toEmbedElemAt .snd)) = rhs)

structure IsInterleavingLike
  (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)]
  (op: EC1 → EC2 → ECR) (inv: ECR → (EC1 × EC2)) (emptyR: ECR) : Prop where
  interleaving: IsInterleaving EC1 EC2 Var1 Var2 Val1 Val2 (fun ec1 ec2 => op ec1 ec2)
  right_inverse: Function.RightInverse inv (Function.uncurry op)
  injective1: Function.Injective (fun ec1 => op ec1 ((inv emptyR).snd))
  injective2: Function.Injective (fun ec2 => op ((inv emptyR).fst) ec2)


namespace IsInterleavingLike

variable {EC1 EC2: Type uec_l} {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l} {ECR: Type uec_r}
         [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2] [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
         [EvalLike ECR (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2)]
         {op: EC1 → EC2 → ECR} {inv: ECR → (EC1 × EC2)} {emptyR: ECR}

@[elab_as_elim]
def recRightEval
  (h: IsInterleavingLike EC1 EC2 VarL1 VarL2 ValL1 ValL2 ECR op inv emptyR)
  {motive: ECR → Sort _}
  (left: (ec1: EC1) → (ec2: EC2) → motive (op ec1 ec2))
  (t: ECR)
  : motive t :=
  let (eq := lm1) ⟨ec1, ec2⟩ := inv t
  left ec1 ec2 |> Eq.subst (by
    have lm2 := h.right_inverse.id
    replace lm1 := congrArg (Function.uncurry op) lm1
    simp only [funext_iff] at lm2
    specialize lm2 t
    simp at lm2
    rewrite [lm2] at lm1
    dsimp at lm1
    exact lm1.symm )

/-
@[reducible]
def toHUnionEval (h: IsInterleavingLike EC1 EC2 VarL1 VarL2 ValL1 ValL2 ECR op inv emptyR) : HasHUnion EC1 EC2 where
-/

end IsInterleavingLike


structure Interleaving
  (EC1 EC2: Type uec_l) (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (ECR: Type uec_r)
  [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2] [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
  [EvalLike ECR (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2)] where
  op (ec1: EC1) (ec2: EC2) : ECR
  inv (ecr: ECR) : (EC1 × EC2)
  emptyR : ECR
  valid: IsInterleavingLike EC1 EC2 VarL1 VarL2 ValL1 ValL2 ECR op inv emptyR




namespace Interleaving

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} {ECR: Type uec_r}
         [HasHUnion Var1 Var2] [HasHUnion Val1 Val2] [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [EvalLike ECR (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)]

theorem inv_injective {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} : Function.Injective (il.inv) :=
  il.valid.right_inverse.leftInverse.injective

theorem op_uncurry_surjective {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} : Function.Surjective (Function.uncurry il.op) :=
  il.valid.right_inverse.surjective

theorem op_eq_op_uncurry {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {ec1: EC1} {ec2: EC2}
  : il.op ec1 ec2 = Function.uncurry il.op (ec1, ec2) :=
  Function.uncurry_apply_pair _ _ _ |>.symm

theorem inv_op_eq_self {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {rv: ECR} : il.op (il.inv rv).fst (il.inv rv).snd = rv := by
  have lm1 := il.valid.right_inverse.eq rv
  dsimp [Function.uncurry_def] at lm1
  exact lm1

theorem inv_op_eq_self_at {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} (rv: ECR) : il.op (il.inv rv).fst (il.inv rv).snd = rv := il.inv_op_eq_self

def emptyAt (il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR) (lb: Label) : lb.casesOn EC1 EC2 :=
  lb.projectProd (il.inv il.emptyR)


@[defeq]
theorem inv_emptyR_eq_emptyAt_prod {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR}
  : il.inv il.emptyR = (il.emptyAt .fst, il.emptyAt .snd) :=
  Label.projectProd_prod_eq.symm


theorem emptyAt_prod_op_uncurry_eq_emptyR {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR}
  : Function.uncurry il.op (il.emptyAt .fst, il.emptyAt .snd) = il.emptyR := by
  dsimp only [← il.inv_emptyR_eq_emptyAt_prod]
  exact il.valid.right_inverse.eq il.emptyR

theorem emptyAt_op_eq_emptyR {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR}
  : il.op (il.emptyAt .fst) (il.emptyAt .snd) = il.emptyR := by
  refine Eq.trans ?_ il.emptyAt_prod_op_uncurry_eq_emptyR
  dsimp


theorem emptyAt_fst_self_op_inv_snd_eq_self {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {ec2: EC2}
  : (il.inv (il.op (il.emptyAt .fst) ec2)).snd = ec2 := by
  simp only [← EvalLike.coe_injective.eq_iff, ← DFunLike.coe_injective.eq_iff, funext_iff]
  intro var
  have lm1 := il.valid.interleaving
  rcases lm1 with ⟨lm1, lm2⟩
/-
  by_cases lm1: ec2 = il.emptyAt .snd
  · subst lm1
    simp [emptyAt_op_eq_emptyR]
    rfl
  · simp only [← EvalLike.coe_injective.eq_iff, ← DFunLike.coe_injective.eq_iff, funext_iff] at lm1 ⊢
    simp at lm1
    rcases lm1 with ⟨var2_1, lm1⟩
    intro var2_2
-/
/-
  rw [← EvalLike.coe_injective.eq_iff]
  rw [← DFunLike.coe_injective.eq_iff]
-/
/-
  have lm1 := il.inv_emptyR_eq_emptyAt_prod
  simp only [Prod.eq_iff_fst_eq_snd_eq] at lm1
  rcases lm1 with ⟨lm1, lm2⟩
  simp only [← lm1]
  have lm3 := il.valid.injective2
-/

/-
  simp only [Prod.eq_iff_fst_eq_snd_eq] at lm1
  rcases lm1 with ⟨lm1, lm2⟩
  simp only [← lm1]
  refine congrArg (Prod.fst) ?_
  rw [il.inv_injective.eq_iff]
  refine Eq.trans ?_ il.emptyAt_op_eq_emptyR
  have lm3 := il.valid.injective2
  simp only [Prod.eq_iff_fst_eq_snd_eq]
-/
/-
  have lm1 := il.valid.injective2
  have lm2 := il.inv_injective.comp lm1
  have lm3 := @lm2.eq_iff
  simp at lm3
-/
  --dsimp [inv_emptyR_eq_emptyAt_prod] at lm2

/-
theorem op_inv_fst_eq_emptyAt_iff {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {ec1: EC1} {ec2: EC2}
  : ((il.inv (il.op ec1 ec2)).fst = il.emptyAt .fst) ↔ (ec1 = il.emptyAt .fst) := by
-/

/-
theorem emptyAt_snd_op_inv_eq {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {ec1: EC1}
  : il.inv (il.op ec1 (il.emptyAt .snd)) = (ec1, (il.emptyAt .snd)) := by
  have lm1 := il.valid.injective1 --.eq_iff' --ec1 (il.emptyAt .fst)
  have lm2 := il.inv_op_eq_self_at il.emptyR
  have lm3 := lm1.eq_iff' (a := ec1) lm2
  rewrite [← il.inv_injective.eq_iff] at lm3
  dsimp [inv_emptyR_eq_emptyAt_prod] at lm3
-/

  --dsimp [inv_emptyR_eq_emptyAt_prod] at lm1
  --simp [inv_emptyR_eq_emptyAt_prod] at lm1
  --rewrite [il.emptyAt_op_eq_emptyR] at lm1
  --dsimp [Function.Injective] at lm1
  --rw [op_eq_op_uncurry]
  --have lm1 := il.op_uncurry_surjective
  --dsimp [Function.Surjective] at lm1



def embedAt (il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR) (lb: Label) : (lb.casesOn EC1 EC2) → ECR :=
  lb.casesOn (motive := fun lb0 => lb0.casesOn EC1 EC2 → ECR)
             (fun ec1 => il.op ec1 (il.emptyAt .snd))
             (fun ec2 => il.op (il.emptyAt .fst) ec2)

@[defeq]
theorem embedAt_fst_eq {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {ec1: EC1} : (il.embedAt .fst ec1) = il.op ec1 (il.emptyAt .snd) := rfl

@[defeq]
theorem embedAt_snd_eq {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {ec2: EC2} : (il.embedAt .snd ec2) = il.op (il.emptyAt .fst) ec2 := rfl


theorem embedAt_injective {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {lb: Label} : Function.Injective (il.embedAt lb) := by
  cases lb <;> dsimp [embedAt, emptyAt, leftEvalAt]
  · exact il.valid.injective1
  · exact il.valid.injective2

theorem embedAt_injective_at {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} (lb: Label) : Function.Injective (il.embedAt lb) := il.embedAt_injective


def liftAt (il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR) (lb: Label) (rv: ECR) : lb.casesOn EC1 EC2 :=
  lb.projectProd (il.inv rv)

/-
theorem embedAt_liftAt_eq {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {lb: Label} (lv: lb.casesOn EC1 EC2)
  : il.liftAt lb (il.embedAt lb lv) = lv := by
  cases lb
  · dsimp [embedAt_fst_eq]
    dsimp [liftAt, Label.projectProd_prod_fst_eq]
    by_cases lm1: lv = il.emptyAt .fst
    · subst lm1
      simp [emptyAt_op_eq_emptyR]
      rfl
    · let x := (lv, il.emptyAt .snd)
      have lm2 : x.fst = lv := rfl
      refine Eq.trans ?_ lm2
      refine congrArg _ ?_
      clear lm2
      subst x
-/

/-
theorem liftAt_embedAt_eq_self {il: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 ECR} {lb: Label} {rv: ECR} (req: rv ∈ Set.range (il.embedAt lb))
  : il.embedAt lb (il.liftAt lb rv) = rv := by
  simp at req
  rcases req with ⟨ec, req⟩
  refine Eq.trans ?_ req
  rw [embedAt_injective.eq_iff]
  replace req := req.symm
  subst req
-/
/-
  cases lb
  · dsimp [liftAt, embedAt, Label.projectProd_prod_fst_eq]
    refine Eq.trans ?_ il.inv_op_eq_self
    congr
    dsimp [emptyAt, Label.projectProd_prod_snd_eq]
    simp at req
    rcases req with ⟨ec, req⟩
    refine congrArg (Prod.snd)
-/

/-

  dsimp [liftAt]
-/
/-
  have lm1 := il.inv_emptyR_eq_emptyAt_prod
  simp only [Prod.eq_iff_fst_eq_snd_eq] at lm1
  rcases lm1 with ⟨lm1, lm2⟩
  dsimp [liftAt]
  have lm3 := il.valid.right_inverse.eq
  have lm4 := lm3 il.emptyR
  have lm5 := @il.valid.injective1.eq_iff'
  cases lb
  · dsimp [Label.projectProd_prod_fst_eq]
-/
/-
    conv =>
      lhs
      arg 1
      arg 2
      rw [← op_eta]
-/
/-
    have lm1 : Function.Injective (il.embedAt .fst) := il.embedAt_injective
    have lm2 : Function.Injective (il.embedAt .snd) := il.embedAt_injective
    dsimp [Function.Injective] at lm1 lm2
    have lm3 := il.valid.right_inverse.id
    simp [funext_iff] at lm3
    have lm4 := lm3 (il.embedAt .fst lv)
    rw [← (il.embedAt_injective (lb := .fst)).eq_iff]
    refine Eq.trans ?_ lm4
    dsimp [embedAt, emptyAt, leftEvalAt, liftAt, Function.uncurry_def]
    have lm5 := lm3 il.emptyR
    dsimp [Function.uncurry_def] at lm5
-/
    --rw
    --dsimp [liftAt, leftEvalAt]
    --dsimp [Function.uncurry_def] at lm1
    --have lm2 := lm1 il.emptyR
    --have lm3 := congrArg il.inv lm2
    --have lm2 := il.valid.injective1
    --dsimp [Function.Injective] at lm2

/-
theorem op_injective : Function.Injective (@op EC1 EC2 VarL1 VarL2 ValL1 ValL2 ECR _ _ _ _ _) := by
  rintro ⟨te1, lm1⟩ ⟨te2, lm2⟩ lm3
  simp at lm3 ⊢
  exact lm3
-/
/-
structure Eval (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2) (ec1: EC1) (ec2: EC2) where
  eval: (HUnionElemAt VarL1 VarL2) → (HUnionElemAt ValL1 ValL2)
  valid: eval = il.op ec1 ec2

def toEval (ec1: EC1) (ec2: EC2) (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2) : Eval il ec1 ec2 where
  eval := il.op ec1 ec2
  valid := rfl

instance {il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2} {ec1: EC1} {ec2: EC2} : EvalLike (Eval il ec1 ec2) (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2) where
  coe x := .mk x.eval
  coe_injective := by rintro ⟨_,_⟩ ⟨_,_⟩; simp
-/

end Interleaving

--def LeftEvalTypeAt (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] [HasHUnion Var1 Var2] [HasHUnion Val1 Val2]

class HasInterleaving (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] where
  var: HasHUnion.Bundle.{uvar_l, uvar_r} Var1 Var2
  val: HasHUnion.Bundle.{uval_l, uval_r} Val1 Val2
  R: Type uec_r
  evalLikeR: EvalLike R (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)
  interleaving: Interleaving EC1 EC2 Var1 Var2 Val1 Val2 R

attribute [reducible, instance] HasInterleaving.var HasInterleaving.val HasInterleaving.evalLikeR

namespace HasInterleaving

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]

def toLiftableEmbedding1 : LiftableEmbedding EC1 (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) :=
  let il : Interleaving EC1 EC2 Var1 Var2 Val1 Val2 _ := interleaving
  let embedding : EC1 ↪ HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2 := ⟨il.embedAt .fst, il.embedAt_injective⟩
  {
    toEmbedding := embedding
    lift rv req := (il.inv rv).fst
    lift_valid lv := by
      subst embedding
      dsimp
      have lm1 := il.valid.injective1
      have lm2 := il.valid.right_inverse.id
      simp [funext_iff] at lm2
      have lm3 := lm2 il.emptyR
      --have lm3 := @lm1.eq_iff
      --simp [Function.uncurry_def] at lm3
  }

/-
instance : HasHUnion EC1 EC2 where
  R := HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2
  fst := {
    toFun := _
    inj' := _
    lift := _
    lift_valid := _
  }
-/

end HasInterleaving

end EvalLike


namespace StandardType

open EvalLike

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]

def SetOfInterleavingValueDomainAt (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) (var: HUnionElemAt Var1 Var2) : Set (HUnionElemAt Val1 Val2) :=
  let s1 : Set Val1 := var.recLiftDiffAt .fst (fun x => sty1.dom x.liftAt) (fun _ => ∅)
  let s2 : Set Val2 := var.recLiftDiffAt .snd (fun x => sty2.dom x.liftAt) (fun _ => ∅)
  HUnionElemAt.setOfHUnion s1 s2


/-
def interleave (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) : StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2) where
  dom := SetOfInterleavingValueDomainAt sty1 sty2
  valid ec var := by
    have lm1 := sty1.valid
    have lm2 := sty2.valid
    let il : Interleaving EC1 EC2 Var1 Var2 Val1 Val2 _ := HasInterleaving.interleaving
    rcases il with ⟨op, lm3⟩
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
