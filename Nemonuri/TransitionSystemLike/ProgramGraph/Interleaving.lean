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

universe uvar_l uval_l uec uvar_r uval_r uec_r

structure IsInterleaving
  (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (EC1 EC2: Type uec) [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
  (VarR: Type uvar_r) (ValR: Type uval_r) [HasHUnion VarL1 VarL2 VarR] [HasHUnion ValL1 ValL2 ValR]
  (op: EC1 → EC2 → (HUnionElemAt VarL1 VarL2 VarR) → (HUnionElemAt ValL1 ValL2 ValR)) : Prop where
  diff_fst (x: HDiffElemAt VarL1 VarL2 VarR .fst) (ec1: EC1) (ec2: EC2) :
    .ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .fst (ec1: Eval VarL1 ValL1) x.toEmbedElem) = op ec1 ec2 (.ofEmbedElem x.toEmbedElem)
  diff_snd (x: HDiffElemAt VarL1 VarL2 VarR .snd) (ec1: EC1) (ec2: EC2) :
    .ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .snd (ec2: Eval VarL2 ValL2) x.toEmbedElem) = op ec1 ec2 (.ofEmbedElem x.toEmbedElem)
  inter (x: HInterElemAt VarL1 VarL2 VarR) (ec1: EC1) (ec2: EC2) :
    let rhs := op ec1 ec2 (x.toUnion)
    (.ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .fst (ec1: Eval VarL1 ValL1) (x.toEmbedElemAt .fst)) = rhs) ∨
    (.ofEmbedElem (EmbedElemAt.mapAt VarL1 VarL2 ValL1 ValL2 .snd (ec2: Eval VarL2 ValL2) (x.toEmbedElemAt .snd)) = rhs)


structure Interleaving
  (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (EC1 EC2: Type uec) [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
  (VarR: Type uvar_r) (ValR: Type uval_r) [HasHUnion VarL1 VarL2 VarR] [HasHUnion ValL1 ValL2 ValR] where
  op (ec1: EC1) (ec2: EC2) : (HUnionElemAt VarL1 VarL2 VarR) → (HUnionElemAt ValL1 ValL2 ValR)
  valid: IsInterleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR op


namespace Interleaving

variable {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l} {EC1 EC2: Type uec} [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
         {VarR: Type uvar_r} {ValR: Type uval_r} [HasHUnion VarL1 VarL2 VarR] [HasHUnion ValL1 ValL2 ValR]

/-
def eval (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR) (ec1: EC1) (ec2: EC2) : (HUnionElemAt VarL1 VarL2 VarR) → (HUnionElemAt ValL1 ValL2 ValR) :=
  il.toEval ec1 ec2
-/


theorem op_injective : Function.Injective (@op VarL1 VarL2 ValL1 ValL2 EC1 EC2 _ _ VarR ValR _ _) := by
  rintro ⟨te1, lm1⟩ ⟨te2, lm2⟩ lm3
  simp at lm3 ⊢
  exact lm3


structure Eval (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR) (ec1: EC1) (ec2: EC2) where
  eval: (HUnionElemAt VarL1 VarL2 VarR) → (HUnionElemAt ValL1 ValL2 ValR)
  valid: eval = il.op ec1 ec2

def toEval (ec1: EC1) (ec2: EC2) (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR) : Eval il ec1 ec2 where
  eval := il.op ec1 ec2
  valid := rfl

theorem toEval_injective {ec1: EC1} {ec2: EC2} : Function.Injective (fun il => (toEval ec1 ec2 il).eval) := by
  intro il1 il2 lm3
  simp [toEval] at lm3
  rcases il1 with ⟨te1, lm1⟩
  rcases il2 with ⟨te2, lm2⟩
  simp at lm3 ⊢
  --rewrite [op_injective.eq_iff] at lm1


--@toEval VarL1 VarL2 ValL1 ValL2 EC1 EC2 _ _ VarR ValR _ _

instance {il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR} {ec1: EC1} {ec2: EC2} : EvalLike (Eval il ec1 ec2) (HUnionElemAt VarL1 VarL2 VarR) (HUnionElemAt ValL1 ValL2 ValR) where
  coe x := .mk x.eval
  coe_injective := by rintro ⟨_,_⟩ ⟨_,_⟩; simp

/-
def evalFlip (ec1: EC1) (ec2: EC2) (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR) := eval il ec1 ec2

theorem evalFlip_injective {ec1: EC1} {ec2: EC2} : Function.Injective (evalFlip ec1 ec2) := by
  intro il1 il2 lm1
  dsimp [evalFlip] at lm1
  have lm2 := @eval_injective VarL1 VarL2 ValL1 ValL2 EC1 EC2 _ _ VarR ValR _ _
  have lm3 := @lm2.eq_iff _ _ _ il1 il2
  simp only [funext_iff] at lm3
-/

/-
inductive OfEvalCarriers
  (VarL1 VarL2: Type uvar_l) (ValL1 ValL2: Type uval_l) (EC1 EC2: Type uec) [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
  (VarR: Type uvar_r) (ValR: Type uval_r) [HasHUnion VarL1 VarL2 VarR] [HasHUnion ValL1 ValL2 ValR]
  : EC1 → EC2 → Type _ where
  | mk (il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR) (ec1: EC1) (ec2: EC2)
    : OfEvalCarriers VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR ec1 ec2
-/
--namespace OfEvalCarriers

/-
variable {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l} {EC1 EC2: Type uec} [EvalLike EC1 VarL1 ValL1] [EvalLike EC2 VarL2 ValL2]
         {VarR: Type uvar_r} {ValR: Type uval_r} [HasHUnion VarL1 VarL2 VarR] [HasHUnion ValL1 ValL2 ValR]
         {ec1: EC1} {ec2: EC2}

def eval (il: OfEvalCarriers VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR ec1 ec2) : (HUnionElemAt VarL1 VarL2 VarR) → (HUnionElemAt ValL1 ValL2 ValR) :=
  il.casesOn (fun il ec1 ec2 => il.toEval ec1 ec2)
-/

/-
theorem eval_injective : Function.Injective (@eval VarL1 VarL2 ValL1 ValL2 EC1 EC2 _ _ VarR ValR _ _ ec1 ec2) := by
  rintro ⟨il1, ec1_1, ec2_1⟩ ⟨il2, ec1_2, ec2_2⟩ lm1
  obtain ⟨te1, lm_v1⟩ := il1
  obtain ⟨te2, lm_v2⟩ := il2
  simp
  dsimp [eval] at lm1
  simp only [funext_iff] at lm1 ⊢
  intro ec1_2 ec2_2 x
  specialize lm1 x
  obtain ⟨lm_v1_1, lm_v1_2, lm_v1_3⟩ := lm_v1
  obtain ⟨lm_v2_1, lm_v2_2, lm_v2_3⟩ := lm_v2
  let decMemVar := DecidableEmbedRange.ofClassicalAt VarL1 VarL2
  let decMemVal := DecidableEmbedRange.ofClassicalAt ValL1 ValL2
  cases x using HUnionElemAt.recDiffInter <;> rename_i x
  · specialize lm_v1_1 x ec1_2 ec2_2
    specialize lm_v2_1 x ec1_2 ec2_2
    exact lm_v1_1.symm.trans lm_v2_1
  · specialize lm_v1_2 x ec1_2 ec2_2
    specialize lm_v2_2 x ec1_2 ec2_2
    exact lm_v1_2.symm.trans lm_v2_2
  · clear lm_v1_1 lm_v2_1 lm_v1_2 lm_v2_2
    specialize lm_v1_3 x
    specialize lm_v2_3 x
    dsimp [HUnionElemAt.ofEmbedElem, HInterElemAt.toEmbedElemAt, HInterElemAt.liftAt, EmbedElemAt.mapAt, EmbedElemAt.bindAt, EmbedElemAt.pureAt, EmbedElemAt.liftAt] at lm_v1_3 lm_v2_3
    simp only [embedAt_liftAt_eq, Subtype.ext_iff] at lm_v1_3 lm_v2_3
    simp only [Subtype.ext_iff] at lm1 ⊢
-/
    --specialize lm_v1_3 ec1_2 ec2_2
    --specialize lm_v2_3 ec1_2 ec2_2
/-
    rcases lm_v1_3 with lm_v1_3 | lm_v1_3
    <;> rcases lm_v2_3 with lm_v2_3 | lm_v2_3
    · exact lm_v1_3.symm.trans lm_v2_3
    ·
-/
/-
      obtain ⟨x, lm2⟩ := x
      simp at lm_v1_3 lm_v2_3
      revert lm2
      simp [hinterSetUnivAt_mem_iff, LeftTypeAt]
      intro xl1 lm1 xl2 lm2 lm3 lm4 lm5
      have lm4_1 := lm4
      conv at lm4_1 => lhs; simp [← lm1, embedAt_liftAt_eq]
      have lm5_1 := lm5
      conv at lm5_1 => lhs; simp [← lm2, embedAt_liftAt_eq]
      rw [← lm4_1, ← lm5_1]
      have lm1_1 := @embedAt_liftAt_eq VarL1 VarL2 VarR _ .fst xl1
      --have lm1_1 := congrArg (liftAt _ _ _ _) lm1
-/
    --have lm2 := lm_v1_3 ec1 ec2
    --have lm3 := lm_v2_3 ec1 ec2
/-
    specialize lm_v1_3 x ec1_2 ec2
    specialize lm_v2_3 x ec1 ec2_2
    dsimp at lm_v1_3 lm_v2_3
    rcases lm_v1_3 with lm_v1_3 | lm_v1_3
    · rcases lm_v2_3 with lm_v2_3 | lm_v2_3
-/
/-
    · rewrite [lm_v1_3] at lm_v2_3
      rcases lm_v2_3 with lm_v2_3 | lm_v2_3
      · subst rhs1
        subst rhs2
        exact lm_v2_3
      · subst rhs1
        subst rhs2
        rewrite [Subtype.ext_iff] at lm_v1_3 lm_v2_3 lm1 ⊢
        dsimp [HUnionElemAt.ofEmbedElem, HInterElemAt.toEmbedElemAt, HInterElemAt.liftAt, EmbedElemAt.mapAt, EmbedElemAt.bindAt, EmbedElemAt.pureAt, EmbedElemAt.liftAt] at lm_v1_3 lm_v2_3
        simp only [embedAt_liftAt_eq] at lm_v1_3 lm_v2_3
-/
        --rw [← lm_v1_3, ← lm_v2_3]
    --specialize lm_v2_1 x ec1_2 ec2_2

  --revert ec1 ec2




--end OfEvalCarriers



/-
def eval (il: Interleaving ec1 ec2 VarR ValR) : (letI := var.hasHUnion; HUnionElemAt VarL1 VarL2 VarR) → ValR :=
  letI := var.hasHUnion; letI := var.memDecidable
  letI := val.hasHUnion; letI := val.memDecidable
  hunionMapAt VarL1 VarL2 VarR ValL1 ValL2 ValR (ec1: VarL1 → ValL1) (ec2: VarL2 → ValL2) il.sel

open DecidableEmbedRange in
theorem eval_injective : Function.Injective (@eval VarL1 VarL2 ValL1 ValL2 ec1 ec2 VarR ValR _ _) := by
  rintro ⟨sel1⟩ ⟨sel2⟩ lm1
  dsimp [eval] at lm1
  simp
  simp only [funext_iff] at lm1 ⊢
  rintro ⟨x, lm2⟩
  let var_hu := var.hasHUnion
  let var_md := var.memDecidable
  specialize lm1 ⟨x, hunionSetUnivAt_mem_of_hinterSetUnivAt_mem lm2⟩
  obtain ⟨lm3, lm4⟩ := hinterSetUnivAt_mem_iff_isInEmbedRangeAt.mp lm2
  simp [hunionMapAt, lm3, lm4] at lm1
  cases lm5: sel1 ⟨x, lm2⟩ <;> cases lm6: sel2 ⟨x, lm2⟩
  <;> try rfl
  · simp [lm5, lm6] at lm1
    revert lm3 lm4
    simp [isInEmbedRangeAt_eq_true_iff, EmbedRangeAt, LeftTypeAt]
    intro var_l1 lm3 var_l2 lm4 lm7
    --have lm8 := @embedAt_injective VarL1 VarL2 VarR _ .fst
    --have lm9 := @embedAt_injective VarL1 VarL2 VarR _ .snd
    conv at lm7 =>
      conv => lhs; simp only [← lm3, embedAt_liftAt_eq]
      conv => rhs; simp only [← lm4, embedAt_liftAt_eq]
    skip

    --simp [isInEmbedRangeAt_eq_true_iff, EmbedRangeAt] at lm3 lm4
-/



end Interleaving



end EvalLike


--structure Interleaving

--namespace Interleaving

--end Interleaving

end Nemonuri.ProgramGraph

end
