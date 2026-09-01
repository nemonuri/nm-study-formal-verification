module

public import Nemonuri.TransitionSystemLike.ProgramGraph.Basic
public import Nemonuri.HasHUnion

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 40

-/

@[expose] public section

namespace Nemonuri.ProgramGraph

open HasHUnion

namespace EvalLike

universe uvar_l uval_l uec_l uvar_r uval_r uec_r

structure IsInterleaving
  (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (EC1 EC2: Type uec_l) [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
  [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2]
  (op: EC1 → EC2 → (HUnionElemAt VarL1 VarL2) → (HUnionElemAt ValL1 ValL2)) : Prop where
  diff_fst (x: HDiffElemAt VarL1 VarL2 .fst) (ec1: EC1) (ec2: EC2) :
    .ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .fst (ec1: Eval VarL1 ValL1) x.toEmbedElem) = op ec1 ec2 (.ofEmbedElem x.toEmbedElem)
  diff_snd (x: HDiffElemAt VarL1 VarL2 .snd) (ec1: EC1) (ec2: EC2) :
    .ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .snd (ec2: Eval VarL2 ValL2) x.toEmbedElem) = op ec1 ec2 (.ofEmbedElem x.toEmbedElem)
  inter (x: HInterElemAt VarL1 VarL2) (ec1: EC1) (ec2: EC2) :
    let rhs := op ec1 ec2 (x.toUnion)
    (.ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .fst (ec1: Eval VarL1 ValL1) (x.toEmbedElemAt .fst)) = rhs) ∨
    (.ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .snd (ec2: Eval VarL2 ValL2) (x.toEmbedElemAt .snd)) = rhs)

structure IsSurjectiveInterleaving
  (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (EC1 EC2: Type uec_l) (ECR: Type uec_r)
  [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2] [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2] [EvalLike ECR (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2)]
  (op: EC1 → EC2 → ECR) : Prop where
  interleaving: IsInterleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 (fun ec1 ec2 => op ec1 ec2)
  surjective: Function.Surjective (Function.uncurry op)

namespace IsSurjectiveInterleaving

variable {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l} {EC1 EC2: Type uec_l} {ECR: Type uec_r}
         [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2] [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
         [EvalLike ECR (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2)]

noncomputable def recRightEvalCarrier
  {op: EC1 → EC2 → ECR} (h: IsSurjectiveInterleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 ECR op)
  {motive: ECR → Sort _}
  (left: (ec1: EC1) → (ec2: EC2) → motive (op ec1 ec2))
  (t: ECR)
  : motive t :=
  match lm1: Classical.choose (h.surjective t) with
  | ⟨ec1, ec2⟩ => left ec1 ec2 |> Eq.subst (by
      have lm2 := Classical.choose_spec (h.surjective t)
      rewrite [lm1] at lm2
      simpa using lm2 )

end IsSurjectiveInterleaving


structure Interleaving
  (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (EC1 EC2: Type uec_l) (ECR: Type uec_r)
  [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2] [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
  [EvalLike ECR (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2)] where
  op (ec1: EC1) (ec2: EC2) : ECR
  valid: IsSurjectiveInterleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 ECR op
  --op_interleaving: IsInterleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 (fun ec1 ec2 => op ec1 ec2)
  --op_surjective: Function.Surjective (Function.uncurry op)



namespace Interleaving

variable {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l} {EC1 EC2: Type uec_l} {ECR: Type uec_r}
         [HasHUnion VarL1 VarL2] [HasHUnion ValL1 ValL2] [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
         [EvalLike ECR (HUnionElemAt VarL1 VarL2) (HUnionElemAt ValL1 ValL2)]



theorem op_injective : Function.Injective (@op VarL1 VarL2 ValL1 ValL2 EC1 EC2 ECR _ _ _ _ _) := by
  rintro ⟨te1, lm1⟩ ⟨te2, lm2⟩ lm3
  simp at lm3 ⊢
  exact lm3

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

class HasInterleaving (EC1 EC2: Type uec_l) (Var1 Var2: Type uvar_l) (Val1 Val2: Type uval_l) [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2] where
  var: HasHUnion.Bundle.{uvar_l, uvar_r} Var1 Var2
  val: HasHUnion.Bundle.{uval_l, uval_r} Val1 Val2
  R: Type uec_r
  evalLikeR: EvalLike R (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2)
  interleaving: Interleaving Var1 Var2 Val1 Val2 EC1 EC2 R

attribute [reducible, instance] HasInterleaving.var HasInterleaving.val HasInterleaving.evalLikeR

end EvalLike


namespace StandardType

open EvalLike

variable {EC1 EC2: Type uec_l} {Var1 Var2: Type uvar_l} {Val1 Val2: Type uval_l} [EvalLike EC1 Var1 Val1] [EvalLike EC2 Var2 Val2]
         [HasInterleaving EC1 EC2 Var1 Var2 Val1 Val2]

def SetOfInterleavingValueDomainAt (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) (var: HUnionElemAt Var1 Var2) : Set (HUnionElemAt Val1 Val2) :=
  let s1 : Set Val1 := var.recLiftDiffAt .fst (fun x => sty1.dom x.liftAt) (fun _ => ∅)
  let s2 : Set Val2 := var.recLiftDiffAt .snd (fun x => sty2.dom x.liftAt) (fun _ => ∅)
  HUnionElemAt.setOfHUnion s1 s2


def interleave (sty1: StandardType EC1 Var1 Val1) (sty2: StandardType EC2 Var2 Val2) : StandardType (HasInterleaving.R EC1 EC2 Var1 Var2 Val1 Val2) (HUnionElemAt Var1 Var2) (HUnionElemAt Val1 Val2) where
  dom := SetOfInterleavingValueDomainAt sty1 sty2
  valid ec var := by
    have lm1 := sty1.valid
    have lm2 := sty2.valid
    let il : Interleaving Var1 Var2 Val1 Val2 EC1 EC2 _ := HasInterleaving.interleaving
    rcases il with ⟨op, lm3⟩
    cases ec using (IsSurjectiveInterleaving.recRightEvalCarrier lm3)
    rename_i ec1 ec2
    specialize lm1 ec1
    specialize lm2 ec2
    cases var using HUnionElemAt.recDiffInter <;> rename_i x
    · let x2 := x.toEmbedElem
      specialize lm1 x2.liftAt
      dsimp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
      refine Or.inl ?_
      simp
      exists ((ec1: Eval Var1 Val1) x2.liftAt)
      refine ⟨?_, ?_⟩
      · simp [HUnionElemAt.recLiftDiffAt, DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, HUnionElemAt.ofEmbedElem]
        exact lm1
      · subst x2
        rcases lm3 with ⟨⟨lm3_1, lm3_2, lm3_3⟩, lm3_4⟩
        specialize lm3_1 x ec1 ec2
        exact lm3_1
    · let x2 := x.toEmbedElem
      specialize lm2 x2.liftAt
      dsimp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
      refine Or.inr ?_
      simp
      exists ((ec2: Eval Var2 Val2) x2.liftAt)
      refine ⟨?_, ?_⟩
      · simp [HUnionElemAt.recLiftDiffAt, DecidableEmbedRange.isInEmbedRangeAt_eq_true_iff, HUnionElemAt.ofEmbedElem]
        exact lm2
      · subst x2
        rcases lm3 with ⟨⟨lm3_1, lm3_2, lm3_3⟩, lm3_4⟩
        specialize lm3_2 x ec1 ec2
        exact lm3_2
    · rcases lm3 with ⟨⟨lm3_1, lm3_2, lm3_3⟩, lm3_4⟩
      clear lm3_1 lm3_2 lm3_4
      specialize lm3_3 x ec1 ec2
      dsimp at lm3_3
      let x1 := x.toEmbedElemAt .fst
      let x2 := x.toEmbedElemAt .snd
      specialize lm1 x1.liftAt
      specialize lm2 x2.liftAt
      rcases lm3_3 with lm3_3 | lm3_3
      · rw [← lm3_3]
        dsimp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
        simp
        refine Or.inl ?_
        exists ((ec1: Eval Var1 Val1) x1.liftAt)
        refine ⟨?_, ?_⟩
        · have lm4 := x.property
          rewrite [hinterSetUnivAt_mem_iff_isInEmbedRangeAt] at lm4
          replace lm4 := lm4.left
          simp [HUnionElemAt.recLiftDiffAt, HInterElemAt.toUnion, lm4]
          subst x1
          conv at lm1 =>
            arg 1
            dsimp [HInterElemAt.toEmbedElemAt, EmbedElemAt.pureAt, HInterElemAt.liftAt]
            simp [liftAt_embedAt_eq]
          exact lm1
        · subst x1
          dsimp [HInterElemAt.toEmbedElemAt, HInterElemAt.liftAt, EmbedElemAt.pureAt, EmbedElemAt.liftAt]
          simp [liftAt_embedAt_eq]
          dsimp [EmbedElemAt.mapAt, EmbedElemAt.bindAt, EmbedElemAt.pureAt, EmbedElemAt.liftAt]
      · rw [← lm3_3]
        dsimp [SetOfInterleavingValueDomainAt, HUnionElemAt.setOfHUnion]
        simp
        refine Or.inr ?_
        exists ((ec2: Eval Var2 Val2) x2.liftAt)
        refine ⟨?_, ?_⟩
        · have lm4 := x.property
          rewrite [hinterSetUnivAt_mem_iff_isInEmbedRangeAt] at lm4
          replace lm4 := lm4.right
          simp [HUnionElemAt.recLiftDiffAt, HInterElemAt.toUnion, lm4]
          subst x2
          conv at lm2 =>
            arg 1
            dsimp [HInterElemAt.toEmbedElemAt, EmbedElemAt.pureAt, HInterElemAt.liftAt]
            simp [liftAt_embedAt_eq]
          exact lm2
        · subst x2
          dsimp [HInterElemAt.toEmbedElemAt, HInterElemAt.liftAt, EmbedElemAt.pureAt, EmbedElemAt.liftAt]
          simp [liftAt_embedAt_eq]
          dsimp [EmbedElemAt.mapAt, EmbedElemAt.bindAt, EmbedElemAt.pureAt, EmbedElemAt.liftAt]



end StandardType


end Nemonuri.ProgramGraph

end
