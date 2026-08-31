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

instance {il: Interleaving VarL1 VarL2 ValL1 ValL2 EC1 EC2 VarR ValR} {ec1: EC1} {ec2: EC2} : EvalLike (Eval il ec1 ec2) (HUnionElemAt VarL1 VarL2 VarR) (HUnionElemAt ValL1 ValL2 ValR) where
  coe x := .mk x.eval
  coe_injective := by rintro ⟨_,_⟩ ⟨_,_⟩; simp

end Interleaving

end EvalLike


--structure Interleaving

--namespace Interleaving

--end Interleaving

end Nemonuri.ProgramGraph

end
