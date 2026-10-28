module

public import Nemonuri.TransitionSystemLike.ProgramGraph.Basic
public import Nemonuri.TransitionSystemLike.Interleaving
public import Nemonuri.Relations.Heterogeneous.SumRelGen.SetLike
public import Nemonuri.Relations.Heterogeneous.SumRelGen.FunHEq

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 40

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.ProgramGraph

open Nemonuri.Relations.Heterogeneous
--universe uvar_l uval_l uec_l uvar_r uval_r uec_r

variable {ECL VarL ValL ValSL ECR VarR ValR ValSR: Type*}
         [SetLike ValSL ValL] [SetLike ValSR ValR] [EvalLike ECL VarL ValL] [EvalLike ECR VarR ValR]


variable (VarL ValL VarR ValR) in
structure Interleaving where
  var: BiUniqueIndicator VarL VarR
  val: BiUniqueIndicator ValL ValR

namespace Interleaving

variable (ECL ECR) in
structure EvalInter (il: Interleaving VarL ValL VarR ValR) where
  left: ECL
  right: ECR
  heq: FunHEq il.var.Rel il.val.Rel ↑left ↑right

namespace EvalInter

variable {il: Interleaving VarL ValL VarR ValR}

def toEval (ei: il.EvalInter ECL ECR) : Eval (SumUnion il.var.Rel) (SumUnion il.val.Rel) :=
  let finter : FunInter il.var.Rel il.val.Rel := ⟨ei.left, ei.right, ei.heq⟩
  ⟨finter.toFun⟩

theorem toEval_injective : Function.Injective (toEval: il.EvalInter ECL ECR → _) := by
  rintro ⟨_,_,_⟩ ⟨_,_,_⟩ lm1
  simp [toEval, FunInter.toFun_injective.eq_iff] at lm1
  simpa using lm1

instance evalLike : EvalLike (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) where
  coe := toEval
  coe_injective := toEval_injective

@[defeq]
theorem apply_def {ei: il.EvalInter ECL ECR} {su: SumUnion il.var.Rel} : ei su = ei.toEval.eval su := rfl

end EvalInter

def AreTypeEquiv (il: Interleaving VarL ValL VarR ValR) (stsL: StandardTypeStruct VarL ValL ValSL) (stsR: StandardTypeStruct VarR ValR ValSR) : Prop :=
  ∀⦃varL varR⦄, (il.var.Rel varL varR) → SumUnion.SetLikeHEq il.val.Rel ValSL ValSR (stsL.dom varL) (stsR.dom varR)

@[defeq]
theorem areTypeEquiv_def {il: Interleaving VarL ValL VarR ValR} {stsL: StandardTypeStruct VarL ValL ValSL} {stsR: StandardTypeStruct VarR ValR ValSR}
  : il.AreTypeEquiv stsL stsR = ∀(varL varR), (il.var.Rel varL varR) → SumUnion.SetLikeHEq il.val.Rel ValSL ValSR (stsL.dom varL) (stsR.dom varR) :=
  rfl

variable (ECL ECR) in
structure AreEvalEquiv (il: Interleaving VarL ValL VarR ValR) : Prop where
  right_exists (ecl: ECL) : ∃(ecr: ECR), FunHEq il.var.Rel il.val.Rel ↑ecl ↑ecr
  left_exists (ecr: ECR) : ∃(ecl: ECL), FunHEq il.var.Rel il.val.Rel ↑ecl ↑ecr


variable {stsL: StandardTypeStruct VarL ValL ValSL} {stsR: StandardTypeStruct VarR ValR ValSR}

open SumUnion in
def toStandardTypeStruct (il: Interleaving VarL ValL VarR ValR) (req: il.AreTypeEquiv stsL stsR) : StandardTypeStruct (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  dom varSu := varSu.funElim (fun l => SetLikeUnion.ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inl (stsL.dom l)))) (fun r => SetLikeUnion.ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inr (stsR.dom r)))) (by
    intro l r lm1
    simp [SetLikeUnion.ofSumUnion]
    refine ofSum_eq_iff_sumEquivGen.mpr ?_
    simp [sumEquivGen_inl_inr_iff]
    exact req lm1 )

open SumUnion in
theorem toStandardTypeStruct_type_safe (il: Interleaving VarL ValL VarR ValR)
  (req1: il.AreTypeEquiv stsL stsR) (req2: ∀(ec: ECL) var, (ec var) ∈ (stsL.dom var)) (req3: ∀(ec: ECR) var, (ec var) ∈ (stsR.dom var))
  (ec: il.EvalInter ECL ECR) (var: SumUnion il.var.Rel) : (ec var) ∈ ((il.toStandardTypeStruct req1).dom var) := by
  rcases ec with ⟨ecl, ecr, lm1⟩
  have lm2 := funHEq_iff.mp lm1
  cases var using SumUnion.indInlInrOfSum with
  | inl l =>
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.mem_def, EvalInter.apply_def,
          SetLikeUnion.ofSumUnion, liftOfSum_ofSum, SetLikeUnion.toSet, SetLikeUnion.toSetUnion, SumUnion.toSet,
          EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂]
    simp [SumUnion.setOfLeftSet_mem_inl_iff_mem]
    exact req2 ecl l
  | inr r =>
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.mem_def, EvalInter.apply_def,
          SetLikeUnion.ofSumUnion, liftOfSum_ofSum, SetLikeUnion.toSet, SetLikeUnion.toSetUnion, SumUnion.toSet,
          EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂]
    simp [SumUnion.setOfRightSet_mem_inr_iff_mem]
    exact req3 ecr r

open SumUnion in
theorem toStandardTypeStruct_eval_exists (il: Interleaving VarL ValL VarR ValR)
  (req1: il.AreTypeEquiv stsL stsR) (req2: il.AreEvalEquiv ECL ECR)
  (req3: ∀var val, (val ∈ stsL.dom var) → ∃(ec: ECL), ec var = val) --(req3: IsStandardType (SetLike.coe ∘ stsL.dom) ECL)
  (req4: ∀var val, (val ∈ stsR.dom var) → ∃(ec: ECR), ec var = val) --(req4: IsStandardType (SetLike.coe ∘ stsR.dom) ECR)
  (var: SumUnion il.var.Rel) (val: SumUnion il.val.Rel) (req5: val ∈ (il.toStandardTypeStruct req1).dom var) : ∃(ec: il.EvalInter ECL ECR), ec var = val := by
  rcases req2 with ⟨lm6, lm7⟩
  cases var using SumUnion.indInlInrOfSum with
  | inl varL =>
    specialize req3 varL
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.ofSumUnion, SetLikeUnion.mem_def,
          SetLikeUnion.toSet, SetLikeUnion.toSetUnion, liftOfSum_ofSum, SumUnion.toSet] at req5
    dsimp [setOfLeftSet] at req5
    rcases req5 with ⟨valL, lm8, lm9⟩
    subst lm9
    specialize req3 valL lm8
    rcases req3 with ⟨ecL, req3⟩
    rewrite [Eq.comm] at req3
    subst req3
    dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [SumUnion.inl_eq_inl_iff_eq]
    specialize lm6 ecL
    rcases lm6 with ⟨ecR, lm6⟩
    exists ⟨ecL, ecR, lm6⟩
  | inr varR =>
    specialize req4 varR
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.ofSumUnion, SetLikeUnion.mem_def,
          SetLikeUnion.toSet, SetLikeUnion.toSetUnion, liftOfSum_ofSum, SumUnion.toSet] at req5
    dsimp [setOfRightSet] at req5
    rcases req5 with ⟨valR, lm8, lm9⟩
    subst lm9
    specialize req4 valR lm8
    rcases req4 with ⟨ecR, req4⟩
    rewrite [Eq.comm] at req4
    subst req4
    dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [SumUnion.inr_eq_inr_iff_eq]
    specialize lm7 ecR
    rcases lm7 with ⟨ecL, lm7⟩
    exists ⟨ecL, ecR, lm7⟩



def toStandardType (il: Interleaving VarL ValL VarR ValR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
  (req1: il.AreTypeEquiv stL.toStruct stR.toStruct) (req2: il.AreEvalEquiv ECL ECR)
  : StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  toStruct := il.toStandardTypeStruct req1
  valid := {
    type_safe := il.toStandardTypeStruct_type_safe req1 stL.valid.type_safe stR.valid.type_safe
    eval_exists := il.toStandardTypeStruct_eval_exists req1 req2 stL.valid.eval_exists stR.valid.eval_exists
  }



  --⟨il.toStandardTypeStruct req1, il.toStandardTypeStruct_type_safe req1 stL.
  --(req1: il.AreTypeEquiv stsL stsR) (req2: il.AreEvalEquiv ECL ECR)
  --: StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) :=
  --⟨il.toStandardTypeStruct req1, il.toStandardTypeStruct_type_safe req1 ⟩


/-
  cases var using SumUnion.indInlInrOfSum with
  | inl varL =>
    specialize lm2 varL
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.ofSumUnion, SetLikeUnion.mem_def,
          SetLikeUnion.toSet, SetLikeUnion.toSetUnion, liftOfSum_ofSum, SumUnion.toSet] at req3
    dsimp [setOfLeftSet] at req3
    rcases req3 with ⟨valL, lm6, lm7⟩
    subst lm7
    specialize lm2 valL lm6
    rcases lm2 with ⟨ecL, lm2⟩
    rewrite [Eq.comm] at lm2
    subst lm2
    dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [SumUnion.inl_eq_inl_iff_eq]
    by_cases lm7: ∃(ecR: ECR), FunHEq il.var.Rel il.val.Rel ecL ecR
    · rcases lm7 with ⟨ecR, lm7⟩
      exists ⟨ecL, ecR, lm7⟩
    · clear lm5
      simp [funHEq_iff] at lm7
      have lm8 := il.dom_heq varL
      dsimp [setLikeHEq_def] at lm8
      simp [setHEq_iff_forall_iff_and_forall_iff] at lm8
      by_cases lm9: ∀varR, ¬il.var.Rel varL varR
      · clear lm8
-/
/-
      simp at lm7
      by_cases lm8: ∃(ecR: ECR) (varR: VarR), il.val.Rel (ecL varL) (ecR varR)
      · rcases lm8 with ⟨ecR, varR, lm8⟩
        simp [funHEq_iff] at lm7
-/
/-
      rcases (inferInstance: Nonempty ECR) with ⟨ecR⟩
      specialize lm7 ecR
      simp [funHEq_iff] at lm7
      rcases lm7 with ⟨varL2, varR, lm7, lm8⟩
      have lm9 ec := lm5 ec (.ofSum (.inr varR))
-/
      --specialize lm7 (Classical.choice inferInstance)
      --simp [funHEq_iff] at lm7
      --rcases lm7 with ⟨varL2, varR, lm7, lm8⟩

/-
  cases var using SumUnion.indInlInrOfSum
  <;> cases val using SumUnion.indInlInrOfSum
  <;> (dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.ofSumUnion, SetLikeUnion.mem_def,
              SetLikeUnion.toSet, SetLikeUnion.toSetUnion, liftOfSum_ofSum, SumUnion.toSet] at req3)
  · rename_i varL valL
    simp [setOfLeftSet_mem_inl_iff_mem] at req3
    have lm5 := il.dom_heq
    dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [SumUnion.inl_eq_inl_iff_eq]
    simp [setLikeHEq_def, setHEq_iff_forall_iff_and_forall_iff] at lm5
    by_cases lm6: ∀l r, ¬il.var.Rel l r
    · clear lm5
      have lm7 := lm2 varL valL req3
      rcases lm7 with ⟨ecL, lm7⟩
      by_contra lm8
      simp at lm8
      replace lm8 ecR lm9 := lm8 ⟨ecL, ecR, lm9⟩
      simp [funHEq_iff, lm6] at lm8
      revert lm8
      simp [lm7]
    · simp at lm6
      rcases lm6 with ⟨varL2, varR2, lm6⟩
      have lm7 := lm2 varL valL req3
      rcases lm7 with ⟨ecL, lm7⟩
      rewrite [Eq.comm] at lm7
      subst lm7
      have lm7 := lm5 varL2 varR2 lm6
      rcases lm7 with ⟨lm7, lm8⟩
      have lm9 := lm7 (ecL varL)
      have lm10 := lm7 (ecL varL2)
      have lm11 := lm1 ecL varL2
      simp at lm11
      simp [lm11] at lm10
      rcases lm10 with ⟨valR, lm10, lm12⟩
      have lm13 := lm4 varR2 valR lm10
      rcases lm13 with ⟨ecR, lm13⟩
      rewrite [Eq.comm] at lm13
      subst lm13
-/
/-
      by_cases lm12: ecL varL ∈ stsL.dom varL2
      · simp [lm12] at lm9
        rcases lm9 with ⟨varR, lm9, lm13⟩
-/
--specialize lm2 varL valL req3
--rcases lm2 with ⟨ec, lm2⟩
/-
    by_cases lm6: ∃varR, il.var.Rel varL varR
    · rcases lm6 with ⟨varR, lm6⟩
      have lm5_1 := lm5 varL varR lm6
      rcases lm5_1 with ⟨lm5_1, lm7⟩
      have lm5_2 := lm5_1 valL
      simp [req3] at lm5_2
      rcases lm5_2 with ⟨valR, lm5_2, lm8⟩
      have lm4_1 := lm4 varR valR lm5_2
      rcases lm4_1 with ⟨ecR, lm4_1⟩
      refine Exists.intro ⟨ec, ecR, ?_⟩ lm2
      simp [funHEq_iff]
      intro l r lm9
      rcases lm5 l r lm9 with ⟨lm10, lm11⟩
      specialize lm1 ec l
      specialize lm3 ecR r
      --specialize lm10 (ec l) --valL
      --specialize lm11 (ecR r) --valR
      --simp at lm1 lm3
      --simp [lm1] at lm10
      --simp [lm3] at lm11
      have lm12 := IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm6 lm9
      by_cases lm13: varL = l
      · subst lm13
        simp at lm12
        subst lm12
        rw [lm2, lm4_1]
        exact lm8
      · simp [lm13] at lm12
        rewrite [Eq.comm] at lm2 lm4_1
        subst lm2 lm4_1
        specialize lm10 (ec varL)
        specialize lm11 (ecR varR)
-/

/-
      rcases lm10 with ⟨r2, lm10, lm12⟩
      rcases lm11 with ⟨l2, lm11, lm13⟩
      have lm14 := IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm12 lm13
      have lm15 := IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm8 lm12
      by_cases lm16: valL = ec l
      · subst lm16
        simp at lm15
        subst lm15
        rewrite [Eq.comm] at lm4_1
        subst lm4_1
        clear lm12
-/
      --specialize lm4 varR
/-
    by_contra lm6
    simp at lm6
    replace lm6 x1 x2 x3 := lm6 ⟨x1, x2, x3⟩
    simp [funHEq_iff] at lm6
-/

    --simp [setOfLeftSet_mem_inl_iff_mem] at req3





end Interleaving


/-
structure Interleaving (VarL ValL ValSL VarR ValR ValSR: Type*) [SetLike ValSL ValL] [SetLike ValSR ValR]
                       (stsL: StandardTypeStruct VarL ValL ValSL) (stsR: StandardTypeStruct VarR ValR ValSR) where
  var: BiUniqueIndicator VarL VarR
  val: BiUniqueIndicator ValL ValR
  dom_heq (varL: VarL) (varR: VarR) : (var.Rel varL varR) → SumUnion.SetLikeHEq val.Rel ValSL ValSR (stsL.dom varL) (stsR.dom varR)
-/



namespace StandardType

--(EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val]




end StandardType


end Nemonuri.ProgramGraph

end
