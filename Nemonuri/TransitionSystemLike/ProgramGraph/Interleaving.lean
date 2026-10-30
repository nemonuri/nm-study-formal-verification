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

namespace AreTypeEquiv

open SumUnion

variable {il: Interleaving VarL ValL VarR ValR} {stsL: StandardTypeStruct VarL ValL ValSL} {stsR: StandardTypeStruct VarR ValR ValSR}

theorem setHEqOf (h: il.AreTypeEquiv stsL stsR) varL varR : (il.var.Rel varL varR) → SetHEq il.val.Rel ↑(stsL.dom varL) ↑(stsR.dom varR) := by
  dsimp [areTypeEquiv_def] at h
  exact h varL varR

#check Classical.skolem



end AreTypeEquiv


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


section ToStandardTypeStruct

open SumUnion SetLikeUnion

variable {il: Interleaving VarL ValL VarR ValR} {req: il.AreTypeEquiv stsL stsR}

@[defeq, sum_simp]
theorem toStandardTypeStruct_dom_inl_eq {varL: VarL} : (il.toStandardTypeStruct req).dom (.ofSum (.inl varL)) = .ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inl (stsL.dom varL))) := by
  dsimp [toStandardTypeStruct, funElim_eq_ofSum]

@[defeq, sum_simp]
theorem toStandardTypeStruct_dom_inr_eq {varR: VarR} : (il.toStandardTypeStruct req).dom (.ofSum (.inr varR)) = .ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inr (stsR.dom varR))) := by
  dsimp [toStandardTypeStruct, funElim_eq_ofSum]

@[sum_simp]
theorem toStandardTypeStruct_isValueSafe_inl_inl_iff {varL: VarL} {valL: ValL}
  : (il.toStandardTypeStruct req).IsValueSafe (.ofSum (.inl varL)) (.ofSum (.inl valL)) ↔ stsL.IsValueSafe varL valL := by
  dsimp [StandardTypeStruct.isValueSafe_def]
  simp [sum_simp]

--(∃varL, stsL.IsValueSafe varL valL ∧ il.var.Rel varL varR)
theorem toStandardTypeStruct_isValueSafe_inr_inl_iff {varR: VarR} {valL: ValL}
  : (il.toStandardTypeStruct req).IsValueSafe (.ofSum (.inr varR)) (.ofSum (.inl valL)) ↔ (∃valR, stsR.IsValueSafe varR valR ∧ il.val.Rel valL valR) := by
  dsimp [StandardTypeStruct.isValueSafe_def]
  simp [sum_simp]

@[sum_simp]
theorem toStandardTypeStruct_isValueSafe_inr_inr_iff {varR: VarR} {valR: ValR}
  : (il.toStandardTypeStruct req).IsValueSafe (.ofSum (.inr varR)) (.ofSum (.inr valR)) ↔ stsR.IsValueSafe varR valR := by
  dsimp [StandardTypeStruct.isValueSafe_def]
  simp [sum_simp]


theorem toStandardTypeStruct_isValueSafe_inl_inr_iff {varL: VarL} {valR: ValR}
  : (il.toStandardTypeStruct req).IsValueSafe (.ofSum (.inl varL)) (.ofSum (.inr valR)) ↔ (∃valL, stsL.IsValueSafe varL valL ∧ il.val.Rel valL valR) := by
  dsimp [StandardTypeStruct.isValueSafe_def]
  simp [sum_simp]

end ToStandardTypeStruct


open SumUnion in
theorem toStandardTypeStruct_type_safe (il: Interleaving VarL ValL VarR ValR)
  (req1: il.AreTypeEquiv stsL stsR) (req2: ∀(ec: ECL) var, (ec var) ∈ (stsL.dom var)) (req3: ∀(ec: ECR) var, (ec var) ∈ (stsR.dom var))
  (ec: il.EvalInter ECL ECR) (var: SumUnion il.var.Rel) : (ec var) ∈ ((il.toStandardTypeStruct req1).dom var) := by
  rcases ec with ⟨ecl, ecr, lm1⟩
  have lm2 := funHEq_iff.mp lm1
  cases var using SumUnion.indInlInrOfSum with
  | inl l =>
    dsimp [sum_simp, EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [sum_simp]
/-
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.mem_def, EvalInter.apply_def,
          SetLikeUnion.ofSumUnion, liftOfSum_ofSum, SetLikeUnion.toSet, SetLikeUnion.toSetUnion, SumUnion.toSet,
          EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂]
    simp [SumUnion.setOfLeftSet_mem_inl_iff_mem]
-/
    exact req2 ecl l
  | inr r =>
    dsimp [sum_simp, EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [sum_simp]
/-
    dsimp [toStandardTypeStruct, funElim_eq_ofSum, SetLikeUnion.mem_def, EvalInter.apply_def,
          SetLikeUnion.ofSumUnion, liftOfSum_ofSum, SetLikeUnion.toSet, SetLikeUnion.toSetUnion, SumUnion.toSet,
          EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂]
    simp [SumUnion.setOfRightSet_mem_inr_iff_mem]
-/
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


/-
theorem toStandardTypeStruct_isValueSafe_iff {il: Interleaving VarL ValL VarR ValR} {req: il.AreTypeEquiv stsL stsR} {var val}
  : (il.toStandardTypeStruct req).IsValueSafe var val := by
  dsimp [toStandardTypeStruct, SetLikeUnion.ofSumUnion, SumUnion.funElim_eq_ofSum]
-/

/-
theorem isValueSetSafe_iff {il: Interleaving VarL ValL VarR ValR} {req: il.AreTypeEquiv stsL stsR}
  :
-/

def toStandardType (il: Interleaving VarL ValL VarR ValR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
  (req1: il.AreTypeEquiv stL.toStruct stR.toStruct) (req2: il.AreEvalEquiv ECL ECR)
  : StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  toStruct := il.toStandardTypeStruct req1
  valid := {
    type_safe := il.toStandardTypeStruct_type_safe req1 stL.valid.type_safe stR.valid.type_safe
    eval_exists := il.toStandardTypeStruct_eval_exists req1 req2 stL.valid.eval_exists stR.valid.eval_exists
  }

/-
open SumUnion in
theorem isValueSafe_exists_iff (il: Interleaving VarL ValL VarR ValR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
  (req1: il.AreTypeEquiv stL.toStruct stR.toStruct) (req2: il.AreEvalEquiv ECL ECR) {varR: VarR} {valL: ValL}
  : (∃valR, stR.IsValueSafe varR valR ∧ il.val.Rel valL valR) ↔ (∃varL, stL.IsValueSafe varL valL ∧ il.var.Rel varL varR) := by
  dsimp [areTypeEquiv_def, setLikeHEq_def] at req1
  simp [setHEq_iff_forall_iff_and_forall_iff, ← StandardTypeStruct.isValueSafe_def] at req1
  constructor
  · rintro ⟨valR, lm1, lm2⟩
    rewrite [stR.eval_exists_iff] at lm1
    rcases lm1 with ⟨ecR, lm1⟩
    rewrite [Eq.comm] at lm1
    subst lm1
    have lm3 := req2.left_exists ecR
    rcases lm3 with ⟨ecL, lm3⟩
    simp [funHEq_iff] at lm3
    simp [stL.eval_exists_iff]
    --by_cases lm4: ∀varL, ¬il.var.Rel varL varR
    --·
-/

/-
variable (ECL ECR) in
open StandardType in
@[reducible]
def toHasProposition.{usl} (il: Interleaving VarL ValL VarR ValR) [HasProposition.{_,_,_,usl} ECL VarL ValL] [HasProposition.{_,_,_,usl} ECR VarR ValR]
  : HasProposition (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) where
  ValS := (SetLikeUnion il.val.Rel ValSL ValSR)
  setLike := inferInstance
-/

/-
variable {il: Interleaving VarL ValL VarR ValR} {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR}
         {req_type_equiv: il.AreTypeEquiv stL.toStruct stR.toStruct} {req_eval_equiv: il.AreEvalEquiv ECL ECR}
-/


/-
def isSpecSafe (il: Interleaving VarL ValL VarR ValR) (req_eval_equiv: il.AreEvalEquiv ECL ECR)
               (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
               (req_type_equiv: il.AreTypeEquiv stL.toStruct stR.toStruct)
               [stL.DecidableSpecSafe] [stR.DecidableSpecSafe] [HasPartialCongruence il.var.Rel]
               (var: SumUnion il.var.Rel) (spec: SetLikeUnion il.val.Rel ValSL ValSR) : Bool :=
    let sumFun : (ValSL ⊕ ValSR) → Bool
      | .inl sal => match var.left? with | .some l => decide (stL.IsValueSetSafe l sal) | .none => .false
      | .inr sar => match var.right? with | .some r => decide (stR.IsValueSetSafe r sar) | .none => .false
    spec.toSumUnion.liftOfSum sumFun (by
      simp [sum_simp]
      --have lm4 := il.toStandardTypeStruct_eval_exists req_type_equiv req_eval_equiv stL.valid.eval_exists stR.valid.eval_exists
      refine ⟨?_, ?_⟩ <;> (
        intro sal sar lm1
        dsimp [SumUnion.setLikeHEq_def] at lm1
        subst sumFun
        dsimp
        generalize lm2: var.left? = l?
        generalize lm3: var.right? = r?
        rcases l? with _ | ⟨l⟩
        <;> rcases r? with _ | ⟨r⟩
        <;> simp )
      · intro lm4
        simp [sum_simp] at lm3
        subst lm3
        simp [sum_simp] at lm2
        simp [StandardTypeStruct.isValueSetSafe_eq_isValueSafe, stR.eval_exists_iff] at lm4
    )
-/
        --dsimp [StandardTypeStruct.isValueSetSafe_eq_isValueSafe, StandardTypeStruct.isValueSafe_def] at lm4



/-
        <;> simp [StandardTypeStruct.isValueSetSafe_def, Set.subset_def]
        <;> (
          cases var using SumUnion.indInlInrOfSum
          <;> simp [sum_simp] at lm2 lm3 ))
      · rewrite [Eq.comm] at lm3
        subst lm3
        simp [StandardType.not_mem_iff_forall_eval_ne]
        by_contra lm5
        simp at lm5
-/
        --have lm3 := req.left_exists

/-
@[reducible]
def toDecidableSpecSafe : (il.toStandardType stL stR req_type_equiv req_eval_equiv).DecidableSpecSafe
-/

/-
@[reducible]
def toConcreteStandardType (il: Interleaving VarL ValL VarR ValR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
  (req1: il.AreTypeEquiv stL.toStruct stR.toStruct) (req2: il.AreEvalEquiv ECL ECR)
  : StandardType.Concrete (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  standardType := il.toStandardType stL stR req1 req2
-/

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
