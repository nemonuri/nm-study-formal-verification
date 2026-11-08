module

public import Nemonuri.TransitionSystemLike.ProgramGraph.Basic
public import Nemonuri.TransitionSystemLike.Interleaving
public import Nemonuri.Relations.Heterogeneous.SumRelGen.SetLike
public import Nemonuri.Relations.Heterogeneous.SumRelGen.FunHEq
public meta import Nemonuri.TransitionSystemLike.ProgramGraph.Attributes

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


section ApplySection

attribute [local simp] toEval FunInter.toFun SumUnion.funElim₂ SumUnion.funElim_eq_ofSum

@[defeq, sum_simp]
theorem apply_inl_eq {ei: il.EvalInter ECL ECR} {varL: VarL} : ei (.ofSum (.inl varL)) = (.ofSum (.inl (ei.left varL))) := by
  dsimp [apply_def]

@[defeq, sum_simp]
theorem apply_inr_eq {ei: il.EvalInter ECL ECR} {varR: VarR} : ei (.ofSum (.inr varR)) = (.ofSum (.inr (ei.right varR))) := by
  dsimp [apply_def]

end ApplySection

end EvalInter


def AreTypeEquivAt (il: Interleaving VarL ValL VarR ValR) (stsL: StandardTypeStruct VarL ValL ValSL) (stsR: StandardTypeStruct VarR ValR ValSR) (varL: VarL) (varR: VarR) : Prop :=
  SumUnion.SetLikeHEq il.val.Rel ValSL ValSR (stsL.dom varL) (stsR.dom varR)

section AreTypeEquivAtSection

variable {il: Interleaving VarL ValL VarR ValR} {stsL: StandardTypeStruct VarL ValL ValSL} {stsR: StandardTypeStruct VarR ValR ValSR} {varL: VarL} {varR: VarR}
         {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR}

@[defeq]
theorem areTypeEquivAt_def : il.AreTypeEquivAt stsL stsR varL varR = SumUnion.SetLikeHEq il.val.Rel ValSL ValSR (stsL.dom varL) (stsR.dom varR) := rfl

open SumUnion in
theorem areTypeEquivAt_iff : Iff (il.AreTypeEquivAt stsL stsR varL varR)
   ((∀valL, stsL.IsValueSafe varL valL → ∃valR, stsR.IsValueSafe varR valR ∧ il.val.Rel valL valR) ∧ (∀valR, stsR.IsValueSafe varR valR → ∃valL, stsL.IsValueSafe varL valL ∧ il.val.Rel valL valR)) := by
   dsimp [areTypeEquivAt_def, setLikeHEq_def, StandardTypeStruct.isValueSafe_def]
   simp [setHEq_iff_forall_iff_imp_and_imp]

namespace AreTypeEquivAt

open SumUnion

theorem setHEq (h: il.AreTypeEquivAt stsL stsR varL varR) : SetHEq il.val.Rel ↑(stsL.dom varL) ↑(stsR.dom varR) := h

theorem right_isValueSafe_and_rel_of_left_isValueSafe (h: il.AreTypeEquivAt stsL stsR varL varR) : ∀valL, stsL.IsValueSafe varL valL → ∃valR, stsR.IsValueSafe varR valR ∧ il.val.Rel valL valR :=
  (areTypeEquivAt_iff.mp h).left

theorem left_isValueSafe_and_rel_of_right_isValueSafe (h: il.AreTypeEquivAt stsL stsR varL varR) : ∀valR, stsR.IsValueSafe varR valR → ∃valL, stsL.IsValueSafe varL valL ∧ il.val.Rel valL valR :=
  (areTypeEquivAt_iff.mp h).right


theorem right_rel_of_left (h: il.AreTypeEquivAt stL.toStruct stR.toStruct varL varR) (ecL: ECL) : ∃(ecR: ECR), il.val.Rel (ecL varL) (ecR varR) := by
  have lm1 := h.right_isValueSafe_and_rel_of_left_isValueSafe
  simp [stL.eval_exists_iff, stR.eval_exists_iff] at lm1
  exact lm1 ecL

theorem left_rel_of_right (h: il.AreTypeEquivAt stL.toStruct stR.toStruct varL varR) (ecR: ECR) : ∃(ecL: ECL), il.val.Rel (ecL varL) (ecR varR) := by
  have lm1 := h.left_isValueSafe_and_rel_of_right_isValueSafe
  simp [stL.eval_exists_iff, stR.eval_exists_iff] at lm1
  exact lm1 ecR

end AreTypeEquivAt

theorem areTypeEquivAt_iff_eval : Iff (il.AreTypeEquivAt stL.toStruct stR.toStruct varL varR)
  ((∀(ecL: ECL), ∃(ecR: ECR), il.val.Rel (ecL varL) (ecR varR)) ∧ (∀(ecR: ECR), ∃(ecL: ECL), il.val.Rel (ecL varL) (ecR varR))) := by
  simp [areTypeEquivAt_iff, stL.eval_exists_iff, stR.eval_exists_iff]


end AreTypeEquivAtSection

def AreTypeEquiv (il: Interleaving VarL ValL VarR ValR) (stsL: StandardTypeStruct VarL ValL ValSL) (stsR: StandardTypeStruct VarR ValR ValSR) : Prop :=
  ∀⦃varL varR⦄, (il.var.Rel varL varR) → il.AreTypeEquivAt stsL stsR varL varR --SumUnion.SetLikeHEq il.val.Rel ValSL ValSR (stsL.dom varL) (stsR.dom varR)

@[defeq]
theorem areTypeEquiv_def {il: Interleaving VarL ValL VarR ValR} {stsL: StandardTypeStruct VarL ValL ValSL} {stsR: StandardTypeStruct VarR ValR ValSR}
  : il.AreTypeEquiv stsL stsR = ∀(varL varR), (il.var.Rel varL varR) → il.AreTypeEquivAt stsL stsR varL varR :=
  rfl


namespace AreTypeEquiv

open SumUnion

variable {il: Interleaving VarL ValL VarR ValR} {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR} {varL: VarL} {varR: VarR}

theorem areTypeEquivAt_of_rel (h: il.AreTypeEquiv stL.toStruct stR.toStruct) (req: il.var.Rel varL varR) : il.AreTypeEquivAt stL.toStruct stR.toStruct varL varR := h req

theorem rel_and_rel_of_rel (h: il.AreTypeEquiv stL.toStruct stR.toStruct) (req: il.var.Rel varL varR) : (∀(ecL: ECL), ∃(ecR: ECR), il.val.Rel (ecL varL) (ecR varR)) ∧ (∀(ecR: ECR), ∃(ecL: ECL), il.val.Rel (ecL varL) (ecR varR)) :=
  areTypeEquivAt_iff_eval.mp (h.areTypeEquivAt_of_rel req)

variable (stL stR) in
theorem of_rel_and_rel_of_rel (req: ∀varL varR, (il.var.Rel varL varR) → (∀(ecL: ECL), ∃(ecR: ECR), il.val.Rel (ecL varL) (ecR varR)) ∧ (∀(ecR: ECR), ∃(ecL: ECL), il.val.Rel (ecL varL) (ecR varR)))
  : il.AreTypeEquiv stL.toStruct stR.toStruct := by
  dsimp [areTypeEquiv_def]
  simp [areTypeEquivAt_iff_eval]
  exact req


/-
variable (stL stR) in
theorem of_funHEq₂ (req1: ∀(ecL: ECL), ∃(ecR: ECR), FunHEq il.var.Rel il.val.Rel ↑ecL ↑ecR)
                   (req2: ∀(ecR: ECR), ∃(ecL: ECL), FunHEq il.var.Rel il.val.Rel ↑ecL ↑ecR)
  : il.AreTypeEquiv stL.toStruct stR.toStruct := by
  dsimp [areTypeEquiv_def]
  simp [funHEq_iff] at req1 req2
  intro varL varR lm1
  simp [areTypeEquivAt_iff_eval]
  refine ⟨?_, ?_⟩
  · intro ecL
    rcases req1 ecL with ⟨ecR, lm2⟩
    specialize lm2 varL varR lm1
    exists ecR
  ·
-/
/-
  dsimp [areTypeEquiv_def]
  simp [funHEq_iff] at req
  intro varL varR lm1
  have lm2 ecL ecR := req ecL ecR varL varR lm1
-/
-- (req1: il.var.Rel varL varR)
/-
theorem funHEq_of_eval_rel (h: il.AreTypeEquiv stL.toStruct stR.toStruct) {ecL: ECL} {ecR: ECR} (req2: il.val.Rel (ecL varL) (ecR varR))
  : FunHEq il.var.Rel il.val.Rel ↑ecL ↑ecR := by
  simp [funHEq_iff]
-/

end AreTypeEquiv

/-
namespace AreTypeEquiv

open SumUnion

variable {il: Interleaving VarL ValL VarR ValR} {stsL: StandardTypeStruct VarL ValL ValSL} {stsR: StandardTypeStruct VarR ValR ValSR}

theorem setHEqOf (h: il.AreTypeEquiv stsL stsR) varL varR : (il.var.Rel varL varR) → SetHEq il.val.Rel ↑(stsL.dom varL) ↑(stsR.dom varR) := by
  dsimp [areTypeEquiv_def] at h
  exact h varL varR

#check Classical.skolem

end AreTypeEquiv
-/

variable (ECL ECR) in
structure IsEvalEquiv (il: Interleaving VarL ValL VarR ValR) : Prop where
  right_exists (ecl: ECL) : ∃(ecr: ECR), FunHEq il.var.Rel il.val.Rel ↑ecl ↑ecr
  left_exists (ecr: ECR) : ∃(ecl: ECL), FunHEq il.var.Rel il.val.Rel ↑ecl ↑ecr

namespace IsEvalEquiv

variable {il: Interleaving VarL ValL VarR ValR} {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR}

variable (stL stR) in
theorem areTypeEquiv (h: il.IsEvalEquiv ECL ECR) : il.AreTypeEquiv stL.toStruct stR.toStruct := by
  dsimp [areTypeEquiv_def]
  intro varL varR lm1
  simp [areTypeEquivAt_iff_eval]
  rcases h with ⟨lm2, lm3⟩
  simp [funHEq_iff] at lm2 lm3
  refine ⟨?_, ?_⟩
  · intro ecL
    specialize lm2 ecL
    rcases lm2 with ⟨ecR, lm2⟩
    specialize lm2 varL varR lm1
    exists ecR
  · intro ecR
    specialize lm3 ecR
    rcases lm3 with ⟨ecL, lm3⟩
    specialize lm3 varL varR lm1
    exists ecL

theorem left_to_right_choice_exists (h: il.IsEvalEquiv ECL ECR) : ∃(f: ECL → ECR), ∀(ecL: ECL), FunHEq il.var.Rel il.val.Rel ecL (f ecL) :=
  Classical.axiomOfChoice h.right_exists

theorem right_to_left_choice_exists (h: il.IsEvalEquiv ECL ECR) : ∃(f: ECR → ECL), ∀(ecR: ECR), FunHEq il.var.Rel il.val.Rel (f ecR) ecR :=
  Classical.axiomOfChoice h.left_exists

theorem of_choice₂ (flr: ECL → ECR) (req1: ∀(ecL: ECL), FunHEq il.var.Rel il.val.Rel ecL (flr ecL)) (frl: ECR → ECL) (req2: ∀(ecR: ECR), FunHEq il.var.Rel il.val.Rel (frl ecR) ecR)
  : il.IsEvalEquiv ECL ECR := by
  refine .mk ?_ ?_
  · intro ecL
    specialize req1 ecL
    exists (flr ecL)
  · intro ecR
    specialize req2 ecR
    exists (frl ecR)

end IsEvalEquiv

theorem isEvalEquiv_iff_skolem {il: Interleaving VarL ValL VarR ValR}
  : (il.IsEvalEquiv ECL ECR) ↔ (∃(flr: ECL → ECR) (frl: ECR → ECL), ∀(ecL: ECL) (ecR: ECR), FunHEq il.var.Rel il.val.Rel ecL (flr ecL) ∧ FunHEq il.var.Rel il.val.Rel (frl ecR) ecR) := by
  constructor
  · intro lm1
    rcases lm1.left_to_right_choice_exists with ⟨flr, lm2⟩
    rcases lm1.right_to_left_choice_exists with ⟨frl, lm3⟩
    exists flr
    exists frl
    intro ecL ecR
    refine ⟨?_, ?_⟩
    · exact lm2 ecL
    · exact lm3 ecR
  · rintro ⟨flr, frl, lm1⟩
    refine IsEvalEquiv.of_choice₂ flr ?_ frl ?_
    · intro ecL
      specialize lm1 ecL (flr ecL)
      exact lm1.left
    · intro ecR
      specialize lm1 (frl ecR) ecR
      exact lm1.right


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


variable {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR} --{varL: VarL} {varR: VarR}
         {req2: il.AreTypeEquiv stL.toStruct stR.toStruct}

@[sum_simp]
theorem toStandardTypeStruct_isValueSafe_inl_inl_iff_of_standardType {varL: VarL} {valL: ValL}
  : (il.toStandardTypeStruct req2).IsValueSafe (.ofSum (.inl varL)) (.ofSum (.inl valL)) ↔ (∃(ecL: ECL), valL = ecL varL) := by
  simp [sum_simp]
  rw [stL.eval_exists_iff]
  simp [Eq.comm]

@[sum_simp]
theorem toStandardTypeStruct_isValueSafe_inr_inl_iff_of_standardType {varR: VarR} {valL: ValL}
  : (il.toStandardTypeStruct req2).IsValueSafe (.ofSum (.inr varR)) (.ofSum (.inl valL)) ↔ (∃(ecR: ECR), il.val.Rel valL (ecR varR)) := by
  simp [toStandardTypeStruct_isValueSafe_inr_inl_iff, stR.eval_exists_iff]

@[sum_simp]
theorem toStandardTypeStruct_isValueSafe_inr_inr_iff_of_standardType {varR: VarR} {valR: ValR}
  : (il.toStandardTypeStruct req2).IsValueSafe (.ofSum (.inr varR)) (.ofSum (.inr valR)) ↔ (∃(ecR: ECR), valR = ecR varR) := by
  simp [sum_simp]
  rw [stR.eval_exists_iff]
  simp [Eq.comm]

@[sum_simp]
theorem toStandardTypeStruct_isValueSafe_inl_inr_iff_of_standardType {varL: VarL} {valR: ValR}
  : (il.toStandardTypeStruct req2).IsValueSafe (.ofSum (.inl varL)) (.ofSum (.inr valR)) ↔ (∃(ecL: ECL), il.val.Rel (ecL varL) valR) := by
  simp [toStandardTypeStruct_isValueSafe_inl_inr_iff, stL.eval_exists_iff]

end ToStandardTypeStruct


section StandardTypeSection

variable {il: Interleaving VarL ValL VarR ValR} {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR}

variable (stL) in
theorem rel_and_left_isValueSafe_iff_eval_rel {varL: VarL} {valR: ValR} : (∃valL, il.val.Rel valL valR ∧ stL.IsValueSafe varL valL) ↔ (∃(ecL: ECL), il.val.Rel (ecL varL) valR) := by
  simp [stL.eval_exists_iff]

variable (stR) in
theorem rel_and_right_isValueSafe_iff_eval_rel {varR: VarR} {valL: ValL} : (∃valR, il.val.Rel valL valR ∧ stR.IsValueSafe varR valR) ↔ (∃(ecR: ECR), il.val.Rel valL (ecR varR)) := by
  simp [stR.eval_exists_iff]

end StandardTypeSection

/-
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
    exact req2 ecl l
  | inr r =>
    dsimp [sum_simp, EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
    simp [sum_simp]
    exact req3 ecr r
-/

open SumUnion in
theorem toStandardTypeStruct_type_safe (il: Interleaving VarL ValL VarR ValR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR) (req: il.AreTypeEquiv stL.toStruct stR.toStruct)
  (ec: il.EvalInter ECL ECR) (var: SumUnion il.var.Rel) : (il.toStandardTypeStruct req).IsValueSafe var (ec var) := by
  generalize lm1: ec var = val
  cases var using SumUnion.indInlInrOfSum with
  | inl varL =>
    cases val using SumUnion.indInlInrOfSum with
    | inl valL =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum] at lm1
      simp [sum_simp] at lm1 ⊢
      rw [← lm1]
      exact stL.isValueSafe_of_eval
    | inr valR =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum] at lm1
      simp [sum_simp] at lm1 ⊢
      exists ec.left
  | inr varR =>
    cases val using SumUnion.indInlInrOfSum with
    | inl valL =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum] at lm1
      simp [sum_simp] at lm1 ⊢
      exists ec.right
    | inr valR =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum] at lm1
      simp [sum_simp] at lm1 ⊢
      rw [← lm1]
      exact stR.isValueSafe_of_eval



open SumUnion in
theorem toStandardTypeStruct_eval_exists (il: Interleaving VarL ValL VarR ValR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR) (req1: il.IsEvalEquiv ECL ECR)
  (var: SumUnion il.var.Rel) (val: SumUnion il.val.Rel) (req2: (il.toStandardTypeStruct (req1.areTypeEquiv stL stR)).IsValueSafe var val) : ∃(ec: il.EvalInter ECL ECR), ec var = val := by
  cases var using SumUnion.indInlInrOfSum with
  | inl varL =>
    cases val using SumUnion.indInlInrOfSum with
    | inl valL =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
      simp [sum_simp] at ⊢ req2
      rcases stL.eval_exists req2 with ⟨ecL, lm1⟩
      rw [← lm1]
      rcases req1.right_exists ecL with ⟨ecR, lm2⟩
      exists ⟨ecL, ecR, lm2⟩
    | inr valR =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
      simp [sum_simp] at ⊢ req2
      rcases req2 with ⟨ecL, lm1⟩
      rcases req1.right_exists ecL with ⟨ecR, lm2⟩
      exists ⟨ecL, ecR, lm2⟩
  | inr varR =>
    cases val using SumUnion.indInlInrOfSum with
    | inl valL =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
      simp [sum_simp] at ⊢ req2
      rcases req2 with ⟨ecR, lm1⟩
      rcases req1.left_exists ecR with ⟨ecL, lm2⟩
      exists ⟨ecL, ecR, lm2⟩
    | inr valR =>
      dsimp [EvalInter.apply_def, EvalInter.toEval, FunInter.toFun, SumUnion.funElim₂, funElim_eq_ofSum]
      simp [sum_simp] at ⊢ req2
      rcases stR.eval_exists req2 with ⟨ecR, lm1⟩
      rw [← lm1]
      rcases req1.left_exists ecR with ⟨ecL, lm2⟩
      exists ⟨ecL, ecR, lm2⟩


/-
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
-/

/-
theorem toStandardTypeStruct_isValueSafe_iff {il: Interleaving VarL ValL VarR ValR} {req: il.AreTypeEquiv stsL stsR} {var val}
  : (il.toStandardTypeStruct req).IsValueSafe var val := by
  dsimp [toStandardTypeStruct, SetLikeUnion.ofSumUnion, SumUnion.funElim_eq_ofSum]
-/

/-
theorem isValueSetSafe_iff {il: Interleaving VarL ValL VarR ValR} {req: il.AreTypeEquiv stsL stsR}
  :
-/

--∃valR, stsR.IsValueSafe varR valR ∧ il.val.Rel valL valR

--variable (stsL) in


def toStandardType (il: Interleaving VarL ValL VarR ValR) (req: il.IsEvalEquiv ECL ECR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
  : StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  toStruct := il.toStandardTypeStruct (req.areTypeEquiv stL stR)
  valid := {
    type_safe := il.toStandardTypeStruct_type_safe stL stR (req.areTypeEquiv stL stR)
    eval_exists := il.toStandardTypeStruct_eval_exists stL stR req
  }

section ToStandardType

open SumUnion

variable {il: Interleaving VarL ValL VarR ValR} {req: il.IsEvalEquiv ECL ECR}
         {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR}

@[defeq, standard_type_norm]
theorem toStandardType_isValueSafe_eq_toStandardTypeStruct_isValueSafe {var: SumUnion il.var.Rel} {val: SumUnion il.val.Rel} --{var val}
  : (il.toStandardType req stL stR).IsValueSafe var val = (il.toStandardTypeStruct (req.areTypeEquiv stL stR)).IsValueSafe var val := by
  dsimp [Interleaving.toStandardType]

@[sum_simp]
theorem toStandardType_isValueSetSafe_inl_inl_iff {varL: VarL} {sl: ValSL}
  : (il.toStandardType req stL stR).IsValueSetSafe (.ofSum (.inl varL)) (.ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inl sl))) ↔
    (stL.IsValueSetSafe varL sl) := by
  dsimp [toStandardType, StandardTypeStruct.isValueSetSafe_eq_isValueSafe]
  simp [sum_simp]
  constructor
  · intro lm1 valL lm2
    specialize lm1 (.ofSum (.inl valL))
    simp [sum_simp] at lm1
    exact lm1 lm2
  · intro lm1 su lm2
    cases su using indInlInrOfSum with
    | inl valL =>
      simp [sum_simp] at lm2 ⊢
      exact lm1 valL lm2
    | inr valR =>
      simp [sum_simp] at lm2 ⊢
      rcases lm2 with ⟨valL, lm2, lm3⟩
      specialize lm1 valL lm2
      rcases stL.eval_exists lm1 with ⟨ecL, lm4⟩
      exists ecL
      rw [lm4]
      exact lm3

@[sum_simp]
theorem toStandardType_isValueSetSafe_inl_inr_iff {varL: VarL} {sr: ValSR}
  : (il.toStandardType req stL stR).IsValueSetSafe (.ofSum (.inl varL)) (.ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inr sr))) ↔
    (∀valR ∈ sr, ∃(ecL: ECL), il.val.Rel (ecL varL) valR) := by
  dsimp [toStandardType, StandardTypeStruct.isValueSetSafe_eq_isValueSafe]
  simp [sum_simp]
  constructor
  · intro lm1 valR lm2
    specialize lm1 (.ofSum (.inr valR))
    simp [sum_simp] at lm1
    exact lm1 lm2
  · intro lm1 su lm2
    cases su using indInlInrOfSum with
    | inl valL =>
      simp [sum_simp] at lm2 ⊢
      rcases lm2 with ⟨valR, lm2, lm3⟩
      specialize lm1 valR lm2
      rcases lm1 with ⟨ecL, lm4⟩
      rw [stL.eval_exists_iff]
      have lm5 := IsBiUnique.leftUnique lm3 lm4
      subst lm5
      exists ecL
    | inr valR =>
      simp [sum_simp] at lm2 ⊢
      exact lm1 valR lm2

@[sum_simp]
theorem toStandardType_isValueSetSafe_inr_inl_iff {varR: VarR} {sl: ValSL}
  : (il.toStandardType req stL stR).IsValueSetSafe (.ofSum (.inr varR)) (.ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inl sl))) ↔
    (∀valL ∈ sl, ∃(ecR: ECR), il.val.Rel valL (ecR varR)) := by
  dsimp [toStandardType, StandardTypeStruct.isValueSetSafe_eq_isValueSafe]
  simp [sum_simp]
  constructor
  · intro lm1 valL lm2
    specialize lm1 (.ofSum (.inl valL))
    simp [sum_simp] at lm1
    exact lm1 lm2
  · intro lm1 su lm2
    cases su using indInlInrOfSum with
    | inl valL =>
      simp [sum_simp] at lm2 ⊢
      exact lm1 valL lm2
    | inr valR =>
      simp [sum_simp] at lm2 ⊢
      rcases lm2 with ⟨valL, lm2, lm3⟩
      specialize lm1 valL lm2
      rcases lm1 with ⟨ecR, lm4⟩
      rw [stR.eval_exists_iff]
      have lm5 := IsBiUnique.rightUnique lm3 lm4
      subst lm5
      exists ecR

@[sum_simp]
theorem toStandardType_isValueSetSafe_inr_inr_iff {varR: VarR} {sr: ValSR}
  : (il.toStandardType req stL stR).IsValueSetSafe (.ofSum (.inr varR)) (.ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inr sr))) ↔
    (stR.IsValueSetSafe varR sr) := by
  dsimp [toStandardType, StandardTypeStruct.isValueSetSafe_eq_isValueSafe]
  simp [sum_simp]
  constructor
  · intro lm1 valR lm2
    specialize lm1 (.ofSum (.inr valR))
    simp [sum_simp] at lm1
    exact lm1 lm2
  · intro lm1 su lm2
    cases su using indInlInrOfSum with
    | inl valL =>
      simp [sum_simp] at lm2 ⊢
      rcases lm2 with ⟨valR, lm2, lm3⟩
      specialize lm1 valR lm2
      rcases stR.eval_exists lm1 with ⟨ecR, lm4⟩
      exists ecR
      rw [lm4]
      exact lm3
    | inr valR =>
      simp [sum_simp] at lm2 ⊢
      exact lm1 valR lm2


end ToStandardType


--StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)

variable (ECL VarL ValL ECR VarR ValR) in
structure Concrete extends toBasic: Interleaving VarL ValL VarR ValR where
  partialCongruenceVal: PartialCongruence toBasic.val.Rel
  partialCongruenceVar: PartialCongruence toBasic.var.Rel
  updateOpLeft: EvalLike.UpdateOP ECL VarL ValL
  updateOpRight: EvalLike.UpdateOP ECR VarR ValR


variable (ECL VarL ValL ECR VarR ValR) in
structure EvalEquiv extends toConcrete: Interleaving.Concrete ECL VarL ValL ECR VarR ValR where
  valid: toBasic.IsEvalEquiv ECL ECR


protected instance setLikeUnionToFintype [∀(sl: ValSL), Fintype sl] [∀(sr: ValSR), Fintype sr] (il: Interleaving VarL ValL VarR ValR) (slu: SetLikeUnion il.val.Rel ValSL ValSR) : Fintype ↑slu :=
  inferInstance

protected instance setLikeUnionToDecidableMem [∀(sl: ValSL), DecidablePred (· ∈ sl)] [∀(sr: ValSR), DecidablePred (· ∈ sr)]
  (il: Interleaving VarL ValL VarR ValR) [HasPartialCongruence il.val.Rel] (slu: SetLikeUnion il.val.Rel ValSL ValSR) (su: SumUnion il.val.Rel) : Decidable (su ∈ slu) :=
  inferInstance

namespace EvalEquiv

section StandardTypeConcrete


instance (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : HasPartialCongruence il.val.Rel := ⟨il.partialCongruenceVal⟩

instance (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : HasPartialCongruence il.var.Rel := ⟨il.partialCongruenceVar⟩

def rightOfLeftEval? (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (ecL: ECL) (varR: VarR) : Option ValR :=
  (HasPartialCongruence.leftOfRel? il.var.Rel varR).bind (fun x => (HasPartialCongruence.rightOfRel? il.val.Rel (ecL x)))

def leftOfRightEval? (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (ecR: ECR) (varL: VarL) : Option ValL :=
  (HasPartialCongruence.rightOfRel? il.var.Rel varL).bind (fun x => (HasPartialCongruence.leftOfRel? il.val.Rel (ecR x)))


theorem rightOfLeftEval?_eq_none_iff {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {ecL varR}
  : (il.rightOfLeftEval? ecL varR = .none) ↔ (∀(varL: VarL), ¬il.var.Rel varL varR) := by
  conv =>
    lhs
    dsimp [rightOfLeftEval?]
    simp [HasPartialCongruence.leftOfRel?_eq_some_iff_rel, HasPartialCongruence.rightOfRel?_eq_none_iff_not_rel]
  constructor
  · intro lm1 varL lm2
    rcases il.valid.right_exists ecL with ⟨ecR, lm3⟩
    simp [funHEq_iff] at lm3
    specialize lm3 _ _ lm2
    specialize lm1 varL lm2 (ecR varR)
    exact lm1 lm3
  · intro lm1 varL lm2 _ _
    specialize lm1 varL
    exact lm1 lm2

theorem leftOfRightEval?_eq_none_iff {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {ecR varL}
  : (il.leftOfRightEval? ecR varL = .none) ↔ (∀(varR: VarR), ¬il.var.Rel varL varR) := by
  conv =>
    lhs
    dsimp [leftOfRightEval?]
    simp [HasPartialCongruence.rightOfRel?_eq_some_iff_rel, HasPartialCongruence.leftOfRel?_eq_none_iff_not_rel]
  constructor
  · intro lm1 varR lm2
    rcases il.valid.left_exists ecR with ⟨ecL, lm3⟩
    simp [funHEq_iff] at lm3
    specialize lm3 _ _ lm2
    specialize lm1 varR lm2 (ecL varL)
    exact lm1 lm3
  · intro lm1 varR lm2 _ _
    specialize lm1 varR
    exact lm1 lm2

theorem rightOfLeftEval?_eq_some_iff {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {ecL varR valR}
  : (il.rightOfLeftEval? ecL varR = .some valR) ↔ (∃(varL: VarL), il.var.Rel varL varR ∧ il.val.Rel (ecL varL) valR) := by
  conv =>
    lhs
    dsimp [rightOfLeftEval?]
    simp [Option.bind_eq_some_iff, HasPartialCongruence.leftOfRel?_eq_some_iff_rel, HasPartialCongruence.rightOfRel?_eq_some_iff_rel]

theorem leftOfRightEval?_eq_some_iff {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {ecR varL valL}
  : (il.leftOfRightEval? ecR varL = .some valL) ↔ (∃(varR: VarR), il.var.Rel varL varR ∧ il.val.Rel valL (ecR varR)) := by
  conv =>
    lhs
    dsimp [leftOfRightEval?]
    simp [Option.bind_eq_some_iff, HasPartialCongruence.leftOfRel?_eq_some_iff_rel, HasPartialCongruence.rightOfRel?_eq_some_iff_rel]



def updateRightEvalOfLeftEval [Fintype VarR] (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (ecL: ECL) (ecR: ECR) : ECR :=
  let fsFun (fs: Finset VarR) : ECR := fs.val.lift (fun ls => il.updateOpRight.updateAllOfPFun (il.rightOfLeftEval? ecL) ls ecR) (by
    intro ls1 ls2 lm1
    have lm2 x := il.updateOpRight.updateAllOfPFun_respects_perm x ls1 ls2 lm1
    simp [funext_iff] at lm2
    exact lm2 _ ecR)
  fsFun Finset.univ

def updateLeftEvalOfRightEval [Fintype VarL] (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (ecR: ECR) (ecL: ECL) : ECL :=
  let fsFun (fs: Finset VarL) : ECL := fs.val.lift (fun ls => il.updateOpLeft.updateAllOfPFun (il.leftOfRightEval? ecR) ls ecL) (by
    intro ls1 ls2 lm1
    have lm2 x := il.updateOpLeft.updateAllOfPFun_respects_perm x ls1 ls2 lm1
    simp [funext_iff] at lm2
    exact lm2 _ ecL)
  fsFun Finset.univ

theorem updateRightEvalOfLeftEval_funHEq [Fintype VarR] (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (ecL: ECL) (ecR: ECR) --(req: FunHEq il.var.Rel il.val.Rel ↑ecL ↑ecR)
  : FunHEq il.var.Rel il.val.Rel ↑ecL ↑(il.updateRightEvalOfLeftEval ecL ecR) := by
  simp [funHEq_iff]
  intro vl vr lm1
  dsimp [updateRightEvalOfLeftEval]
  rename Fintype VarR => ft
  rcases ft with ⟨⟨ls, lm2⟩, lm3⟩
  dsimp [Finset.univ]
  cases ls using Quotient.ind
  rename_i ls
  dsimp only [Quotient.lift_mk]
  simp at lm2 lm3
  specialize lm3 vr
  generalize lm4: il.rightOfLeftEval? ecL = pf
  rcases lm5: pf vr with _ | val
  · subst lm4
    have lm6 := rightOfLeftEval?_eq_none_iff.mp lm5 vl
    contradiction
  · have lm6 := il.updateOpRight.updateAllOfPFun_eq_apply_of_mem_and_eq_some pf vr ls lm3 val lm5 ecR
    rw [lm6]
    rewrite [Eq.comm] at lm4
    subst lm4
    rcases rightOfLeftEval?_eq_some_iff.mp lm5 with ⟨varR, lm7, lm8⟩
    have lm9 := IsBiUnique.leftUnique lm1 lm7
    rw [lm9]
    exact lm8



theorem updateLeftEvalOfRightEval_funHEq [Fintype VarL] (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (ecL: ECL) (ecR: ECR) --(req: FunHEq il.var.Rel il.val.Rel ↑ecL ↑ecR)
  : FunHEq il.var.Rel il.val.Rel ↑(il.updateLeftEvalOfRightEval ecR ecL) ↑ecR := by
  simp [funHEq_iff]
  intro vl vr lm1
  dsimp [updateLeftEvalOfRightEval]
  rename Fintype VarL => ft
  rcases ft with ⟨⟨ls, lm2⟩, lm3⟩
  dsimp [Finset.univ]
  cases ls using Quotient.ind
  rename_i ls
  dsimp only [Quotient.lift_mk]
  simp at lm2 lm3
  specialize lm3 vl
  generalize lm4: il.leftOfRightEval? ecR = pf
  rcases lm5: pf vl with _ | val
  · subst lm4
    have lm6 := leftOfRightEval?_eq_none_iff.mp lm5 vr
    contradiction
  · have lm6 := il.updateOpLeft.updateAllOfPFun_eq_apply_of_mem_and_eq_some pf vl ls lm3 val lm5 ecL
    rw [lm6]
    rewrite [Eq.comm] at lm4
    subst lm4
    rcases leftOfRightEval?_eq_some_iff.mp lm5 with ⟨varR, lm7, lm8⟩
    have lm9 := IsBiUnique.rightUnique lm1 lm7
    rw [lm9]
    exact lm8


def mergeEffect [Fintype VarR] [Fintype VarL] (il: EvalEquiv ECL VarL ValL ECR VarR ValR) {ActL ActR: Type*} (effL: ActL → ECL → ECL) (effR: ActR → ECR → ECR) (actSum: ActL ⊕ ActR) (ec: il.EvalInter ECL ECR) : il.EvalInter ECL ECR :=
  match actSum with
  | .inl actL =>
    let ecLNext : ECL := effL actL ec.left
    ⟨ecLNext, il.updateRightEvalOfLeftEval ecLNext ec.right, il.updateRightEvalOfLeftEval_funHEq _ _⟩
  | .inr actR =>
    let ecRNext : ECR := effR actR ec.right
    ⟨il.updateLeftEvalOfRightEval ecRNext ec.left, ecRNext, il.updateLeftEvalOfRightEval_funHEq _ _⟩



variable [StandardType.Concrete ECL VarL ValL ValSL] [StandardType.Concrete ECR VarR ValR ValSR]

open StandardType hiding Concrete
open StandardType.Concrete

variable (ValSL ValSR) in
protected def toStandardType
  (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) :=
  il.toBasic.toStandardType il.valid (standardTypeAt ECL ValSL) (standardTypeAt ECR ValSR)

@[defeq, standard_type_norm]
theorem toStandardType_def {il: EvalEquiv ECL VarL ValL ECR VarR ValR} : il.toStandardType ValSL ValSR = il.toBasic.toStandardType il.valid (standardTypeAt ECL ValSL) (standardTypeAt ECR ValSR) :=
  rfl

variable (ValSL ValSR) in
instance toStandardTypeConcrete (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : StandardType.Concrete (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  standardType := il.toStandardType ValSL ValSR
  decidableEq := inferInstance
  specToFintype := il.toBasic.setLikeUnionToFintype

@[defeq, standard_type_norm]
theorem standardTypeAt_eq_toStandardType {il: EvalEquiv ECL VarL ValL ECR VarR ValR}
  : (standardTypeAt (il.EvalInter ECL ECR) (SetLikeUnion il.val.Rel ValSL ValSR)) = il.toStandardType ValSL ValSR := by
  dsimp [standardTypeAt_def, StandardType.Concrete.standardType]

/-
@[defeq]
theorem standardTypeAt_eq_toBasic_toStandardType {il: EvalEquiv ECL VarL ValL ECR VarR ValR}
  : (standardTypeAt (il.EvalInter ECL ECR) (SetLikeUnion il.val.Rel ValSL ValSR)) = il.toBasic.toStandardType il.valid (standardTypeAt ECL ValSL) (standardTypeAt ECR ValSR) := by
  dsimp [standardTypeAt_eq_toStandardType, EvalEquiv.toStandardType]
-/

variable (ValSL ValSR) in
abbrev AtomicPropUnion (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Type _ := AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)


def atomicPropOfLeft (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (apL: AtomicProp ECL VarL ValL ValSL) : il.AtomicPropUnion ValSL ValSR where
  var := .ofSum (.inl apL.var)
  spec := .ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inl apL.spec))
  valid := by
    refine .mk ?_
    simp [standard_type_norm, sum_simp]
    exact apL.valid.spec_safe

def atomicPropOfRight (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (apR: AtomicProp ECR VarR ValR ValSR) : il.AtomicPropUnion ValSL ValSR where
  var := .ofSum (.inr apR.var)
  spec := .ofSumUnion il.val.Rel ValSL ValSR (.ofSum (.inr apR.spec))
  valid := by
    refine .mk ?_
    simp [standard_type_norm, sum_simp]
    exact apR.valid.spec_safe

theorem atomicPropOfLeft_injective (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Function.Injective (il.atomicPropOfLeft: AtomicProp ECL VarL ValL ValSL → il.AtomicPropUnion ValSL ValSR) := by
  intro ap1 ap2 lm3
  rcases ap1 with ⟨⟨v1, s1⟩, lm1⟩
  rcases ap2 with ⟨⟨v2, s2⟩, lm2⟩
  simp
  simp [atomicPropOfLeft, sum_simp] at lm3
  rcases lm3 with ⟨lm3, lm4⟩
  refine ⟨lm3, ?_⟩
  rewrite [SetLike.ext_iff] at ⊢ lm4
  intro v
  specialize lm4 (.ofSum (.inl v))
  simp [sum_simp] at lm4
  exact lm4

theorem atomicPropOfRight_injective (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Function.Injective (il.atomicPropOfRight: AtomicProp ECR VarR ValR ValSR → il.AtomicPropUnion ValSL ValSR) := by
  intro ap1 ap2 lm3
  rcases ap1 with ⟨⟨v1, s1⟩, lm1⟩
  rcases ap2 with ⟨⟨v2, s2⟩, lm2⟩
  simp
  simp [atomicPropOfRight, sum_simp] at lm3
  rcases lm3 with ⟨lm3, lm4⟩
  refine ⟨lm3, ?_⟩
  rewrite [SetLike.ext_iff] at ⊢ lm4
  intro v
  specialize lm4 (.ofSum (.inr v))
  simp [sum_simp] at lm4
  exact lm4


@[pl_simp]
theorem atomicPropOfLeft_isEvalSpecSafe_iff (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (apL: AtomicProp ECL VarL ValL ValSL) (ec: il.EvalInter ECL ECR)
  : ((il.atomicPropOfLeft apL: il.AtomicPropUnion ValSL ValSR).IsEvalSpecSafe ec) ↔ apL.IsEvalSpecSafe ec.left := by
  open SumUnion in
  dsimp [pl_simp, atomicPropOfLeft, AtomicPropStruct.isEvalSpecSafe_def]
  simp [sum_simp]

@[pl_simp]
theorem atomicPropOfRight_isEvalSpecSafe_iff (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (apR: AtomicProp ECR VarR ValR ValSR) (ec: il.EvalInter ECL ECR)
  : ((il.atomicPropOfRight apR: il.AtomicPropUnion ValSL ValSR).IsEvalSpecSafe ec) ↔ apR.IsEvalSpecSafe ec.right := by
  open SumUnion in
  dsimp [pl_simp, atomicPropOfRight, AtomicPropStruct.isEvalSpecSafe_def]
  simp [sum_simp]

open SumUnion in
theorem atomicPropOfLeft_eq_atomicPropOfRight_iff {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {apL: AtomicProp ECL VarL ValL ValSL} {apR: AtomicProp ECR VarR ValR ValSR}
  : (il.atomicPropOfLeft apL = il.atomicPropOfRight apR) ↔ (il.var.Rel apL.var apR.var ∧ SetLikeHEq il.val.Rel ValSL ValSR apL.spec apR.spec) := by
  dsimp [atomicPropOfLeft, atomicPropOfRight]
  simp [sum_simp, SetLike.ext_iff]
  intro lm1
  dsimp [setLikeHEq_def, setOfLeftSet, setOfRightSet]
  simp only [setHEq_iff_forall_iff]

/-
def areAtomicPropEq (il: EvalEquiv ECL VarL ValL ECR VarR ValR) [DecidableEq (SumUnion il.var.Rel)] [DecidableEq (SetLikeUnion il.val.Rel ValSL ValSR)]
  (ap1 ap2: AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)) : Bool :=
  (decide (ap1.var = ap2.var)) && (decide (ap1.spec = ap2.spec))

theorem areAtomicPropEq_eq_true_iff_eq {il: EvalEquiv ECL VarL ValL ECR VarR ValR} [DecidableEq (SumUnion il.var.Rel)] [DecidableEq (SetLikeUnion il.val.Rel ValSL ValSR)]
  {ap1 ap2: AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)}
  : (il.areAtomicPropEq ap1 ap2 = .true) ↔ (ap1 = ap2) := by
  dsimp [areAtomicPropEq]
  rcases ap1 with ⟨⟨_, _⟩, _⟩
  rcases ap2 with ⟨⟨_, _⟩, _⟩
  simp

instance decidableAtomicPropEq (il: EvalEquiv ECL VarL ValL ECR VarR ValR) [DecidableEq (SumUnion il.var.Rel)] [DecidableEq (SetLikeUnion il.val.Rel ValSL ValSR)]
  : DecidableEq (AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)) :=
  fun _ _ => decidable_of_decidable_of_iff (il.areAtomicPropEq_eq_true_iff_eq)
-/

open StandardType.AtomicProp

variable (ValSL ValSR) in
def toAtomicPropSigletonOPStruct [HasSingletonOP ECL VarL ValL ValSL] [HasSingletonOP ECR VarR ValR ValSR]
  (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : SingletonOPStruct (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) :=
  let sumFun (var: VarL ⊕ VarR) (val: SumUnion il.val.Rel) (req: (il.toStandardType ValSL ValSR).IsValueSafe (.ofSum var) val) : AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) :=
    match var with
    | .inl varL =>
      match lm1: val.left? with
      | .some valL => il.atomicPropOfLeft (HasSingletonOP.singletonOP.op varL valL (by
          simp [sum_simp] at lm1
          subst lm1
          simp [standard_type_norm, sum_simp] at req
          exact req ))
      | .none => absurd lm1 (by
          simp [sum_simp] at lm1
          rcases lm1 with ⟨valR, lm1, lm2⟩
          subst lm1
          simp [standard_type_norm, sum_simp] at req
          rcases req with ⟨ecL, lm3⟩
          specialize lm2 (ecL varL)
          contradiction )
    | .inr varR =>
      match lm1: val.right? with
      | .some valR => il.atomicPropOfRight (HasSingletonOP.singletonOP.op varR valR (by
          simp [sum_simp] at lm1
          subst lm1
          simp [standard_type_norm, sum_simp] at req
          exact req ))
      | .none => absurd lm1 (by
          simp [sum_simp] at lm1
          rcases lm1 with ⟨valL, lm1, lm2⟩
          subst lm1
          simp [standard_type_norm, sum_simp] at req
          rcases req with ⟨ecR, lm3⟩
          specialize lm2 (ecR varR)
          contradiction )
  { op var val req := Quotient.pliftOn var (fun s h => sumFun s val (by
      subst h
      dsimp [standard_type_norm] at req
      dsimp [SumUnion.ofSum_def]
      exact req
    )) (by
      intro s1 s2 lm1 lm2 lm3
      change SumEquivGen il.var.Rel s1 s2 at lm3
      rewrite [← SumUnion.ofSum_def] at lm1 lm2
      rcases s1 with ⟨l1⟩ | ⟨r1⟩
      <;> rcases s2 with ⟨l2⟩ | ⟨r2⟩
      <;> (subst sumFun; dsimp; simp [sum_simp] at lm3)
      · subst lm3
        rfl
      · split <;> split
        · rename_i lm4 _ lm5
          have lm6 := val.rel_of_left?_eq_some_and_right?_eq_some lm4 lm5
          simp [atomicPropOfLeft_eq_atomicPropOfRight_iff, HasSingletonOP.var_eq]
          refine ⟨lm3, ?_⟩
          dsimp [SumUnion.setLikeHEq_def]
          simp [HasSingletonOP.spec_eq_singleton, SumUnion.setHEq_iff_forall_iff_imp_and_imp]
          exact lm6
        · rename_i lm4 lm5
          have lm6 := val.not_rel_of_left?_eq_some_and_right?_eq_none lm4 lm5
          have lm7 := val.left?_eq_some_iff_eq.mp lm4
          subst lm7 lm2
          simp [standard_type_norm, sum_simp] at req
          rcases req with ⟨ecR, lm8⟩
          specialize lm6 (ecR r2)
          contradiction
        · rename_i lm4 _ lm5
          have lm6 := val.not_rel_of_left?_eq_none_and_right?_eq_some lm4 lm5
          have lm7 := val.right?_eq_some_iff_eq.mp lm5
          subst lm7 lm1
          simp [standard_type_norm, sum_simp] at req
          rcases req with ⟨ecL, lm8⟩
          specialize lm6 (ecL l1)
          contradiction
        · rfl
      · symm
        split <;> split
        · rename_i lm4 _ lm5
          have lm6 := val.rel_of_left?_eq_some_and_right?_eq_some lm4 lm5
          simp [atomicPropOfLeft_eq_atomicPropOfRight_iff, HasSingletonOP.var_eq]
          refine ⟨lm3, ?_⟩
          dsimp [SumUnion.setLikeHEq_def]
          simp [HasSingletonOP.spec_eq_singleton, SumUnion.setHEq_iff_forall_iff_imp_and_imp]
          exact lm6
        · rename_i lm4 lm5
          have lm6 := val.not_rel_of_left?_eq_some_and_right?_eq_none lm4 lm5
          have lm7 := val.left?_eq_some_iff_eq.mp lm4
          subst lm7 lm1
          simp [standard_type_norm, sum_simp] at req
          rcases req with ⟨ecR, lm8⟩
          specialize lm6 (ecR r1)
          contradiction
        · rename_i lm4 _ lm5
          have lm6 := val.not_rel_of_left?_eq_none_and_right?_eq_some lm4 lm5
          have lm7 := val.right?_eq_some_iff_eq.mp lm5
          subst lm7 lm2
          simp [standard_type_norm, sum_simp] at req
          rcases req with ⟨ecL, lm8⟩
          specialize lm6 (ecL l2)
          contradiction
        · rfl
      · subst lm3
        rfl )}


protected instance hasAtomicPropSigletonOP [HasSingletonOP ECL VarL ValL ValSL] [HasSingletonOP ECR VarR ValR ValSR] (il: EvalEquiv ECL VarL ValL ECR VarR ValR)
  : HasSingletonOP (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  singletonOP := .mk (il.toAtomicPropSigletonOPStruct ValSL ValSR) (by
    refine .mk ?_ ?_
    · intro var val lm1
      dsimp [toAtomicPropSigletonOPStruct]
      cases var using SumUnion.indInlInrOfSum with
      | inl varL =>
        dsimp [SumUnion.ofSum_def, Quotient.pliftOn, Quot.pliftOn, Quot.rec]
        split
        · dsimp [atomicPropOfLeft, ← SumUnion.ofSum_def]
          simp [sum_simp]
          exact HasSingletonOP.var_eq
        · rename_i lm2
          simp [sum_simp] at lm2
          rcases lm2 with ⟨varR, lm2, lm3⟩
          subst lm2
          simp [standard_type_norm, sum_simp] at lm1
          rcases lm1 with ⟨ecL, lm1⟩
          specialize lm3 (ecL varL)
          contradiction
      | inr varR =>
        dsimp [SumUnion.ofSum_def, Quotient.pliftOn, Quot.pliftOn, Quot.rec]
        split
        · dsimp [atomicPropOfRight, ← SumUnion.ofSum_def]
          simp [sum_simp]
          exact HasSingletonOP.var_eq
        · rename_i lm2
          simp [sum_simp] at lm2
          rcases lm2 with ⟨varL, lm2, lm3⟩
          subst lm2
          simp [standard_type_norm, sum_simp] at lm1
          rcases lm1 with ⟨ecR, lm1⟩
          specialize lm3 (ecR varR)
          contradiction
    · intro var val lm1
      refine Set.ext ?_
      intro val2
      dsimp [toAtomicPropSigletonOPStruct]
      cases var using SumUnion.indInlInrOfSum with
      | inl varL =>
        dsimp [SumUnion.ofSum_def, Quotient.pliftOn, Quot.pliftOn, Quot.rec]
        simp
        split
        · rename_i lm2
          simp [sum_simp] at lm2
          subst lm2
          dsimp [atomicPropOfLeft]
          simp [sum_simp, HasSingletonOP.spec_eq_singleton]
          cases val2 using SumUnion.indInlInrOfSum <;> simp [sum_simp]
        · rename_i lm2
          simp [sum_simp] at lm2
          rcases lm2 with ⟨varR, lm2, lm3⟩
          subst lm2
          simp [standard_type_norm, sum_simp] at lm1
          rcases lm1 with ⟨ecL, lm1⟩
          specialize lm3 (ecL varL)
          contradiction
      | inr varR =>
        dsimp [SumUnion.ofSum_def, Quotient.pliftOn, Quot.pliftOn, Quot.rec]
        simp
        split
        · rename_i lm2
          simp [sum_simp] at lm2
          subst lm2
          dsimp [atomicPropOfRight]
          simp [sum_simp, HasSingletonOP.spec_eq_singleton]
          cases val2 using SumUnion.indInlInrOfSum <;> simp [sum_simp]
        · rename_i lm2
          simp [sum_simp] at lm2
          rcases lm2 with ⟨varL, lm2, lm3⟩
          subst lm2
          simp [standard_type_norm, sum_simp] at lm1
          rcases lm1 with ⟨ecR, lm1⟩
          specialize lm3 (ecR varR)
          contradiction )


end StandardTypeConcrete

section StandardTypeConcreteFinite

open StandardType hiding Concrete
variable [ConcreteFinite ECL VarL ValL ValSL] [ConcreteFinite ECR VarR ValR ValSR]


variable (ValSL ValSR) in
protected instance toStandardTypeConcreteFinite
  (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : ConcreteFinite (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  toConcrete := il.toStandardTypeConcrete ValSL ValSR
  hasSingletonOP := il.hasAtomicPropSigletonOP
  decidableEqVar := inferInstance
  fintypeVar := SumUnion.fintype il.var.Rel
  --fintypeSpec := SetLikeUnion.fintype


example (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : DecidableEq (SetLikeUnion il.val.Rel ValSL ValSR) := inferInstance

instance (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : DecidableEq (AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)) := fun _ _ => inferInstance


open PropositionalLogics


example (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : DecidableEq (Formula (AtomicProp (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR))) := Formula.instDecidableEq

example (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : DecidableEq (Cond (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR)) := fun _ _ => inferInstance


def formulaOfLeft (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Formula (AtomicProp ECL VarL ValL ValSL) → Formula (il.AtomicPropUnion ValSL ValSR)
  | .true => .true
  | .atom ap => .atom (il.atomicPropOfLeft ap)
  | .neg fml => .neg (il.formulaOfLeft fml)
  | .and fml1 fml2 => .and (il.formulaOfLeft fml1) (il.formulaOfLeft fml2)

def formulaOfRight (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Formula (AtomicProp ECR VarR ValR ValSR) → Formula (il.AtomicPropUnion ValSL ValSR)
  | .true => .true
  | .atom ap => .atom (il.atomicPropOfRight ap)
  | .neg fml => .neg (il.formulaOfRight fml)
  | .and fml1 fml2 => .and (il.formulaOfRight fml1) (il.formulaOfRight fml2)

--set_option trace.Meta.synthInstance true in
example (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : IndicatorLike (il.EvalInter ECL ECR) (il.AtomicPropUnion ValSL ValSR) := inferInstance

section FormulaSimpSection

variable {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {ei: il.EvalInter ECL ECR}

@[pl_simp]
theorem formulaOfLeft_isSat_iff_isSat (fml: Formula (AtomicProp ECL VarL ValL ValSL)) : (ei ⊨ₚ (il.formulaOfLeft fml)) ↔ (ei.left ⊨ₚ fml) := by
  rcases fml with _ | _ | ⟨fml⟩ | ⟨fmlL, fmlR⟩
  <;> (dsimp [formulaOfLeft]; simp [pl_simp])
  · refine not_iff_not.mpr ?_
    exact formulaOfLeft_isSat_iff_isSat fml
  · have lm1 := formulaOfLeft_isSat_iff_isSat fmlL
    have lm2 := formulaOfLeft_isSat_iff_isSat fmlR
    rw [lm1, lm2]

@[pl_simp]
theorem formulaOfRight_isSat_iff_isSat (fml: Formula (AtomicProp ECR VarR ValR ValSR)) : (ei ⊨ₚ (il.formulaOfRight fml)) ↔ (ei.right ⊨ₚ fml) := by
  rcases fml with _ | _ | ⟨fml⟩ | ⟨fmlL, fmlR⟩
  <;> (dsimp [formulaOfRight]; simp [pl_simp])
  · refine not_iff_not.mpr ?_
    exact formulaOfRight_isSat_iff_isSat fml
  · have lm1 := formulaOfRight_isSat_iff_isSat fmlL
    have lm2 := formulaOfRight_isSat_iff_isSat fmlR
    rw [lm1, lm2]

end FormulaSimpSection


theorem formulaOfLeft_isCond_of_isCond {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {fml: Formula (AtomicProp ECL VarL ValL ValSL)} (req: IsCond _ _ _ _ fml)
  : IsCond _ _ _ _ (il.formulaOfLeft fml) := by
  rcases req with _ | ⟨ap, fml, lm1⟩
  · dsimp [formulaOfLeft]
    exact .nil
  · dsimp [formulaOfLeft]
    refine .cons (il.atomicPropOfLeft ap) (il.formulaOfLeft fml) ?_
    exact formulaOfLeft_isCond_of_isCond lm1

theorem formulaOfRight_isCond_of_isCond {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {fml: Formula (AtomicProp ECR VarR ValR ValSR)} (req: IsCond _ _ _ _ fml)
  : IsCond _ _ _ _ (il.formulaOfRight fml) := by
  rcases req with _ | ⟨ap, fml, lm1⟩
  · dsimp [formulaOfRight]
    exact .nil
  · dsimp [formulaOfRight]
    refine .cons (il.atomicPropOfRight ap) (il.formulaOfRight fml) ?_
    exact formulaOfRight_isCond_of_isCond lm1

theorem formulaOfLeft_injective (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Function.Injective (il.formulaOfLeft) := by
  rintro fml1 fml2 lm1
  rcases fml1 with _ | ⟨ap1⟩ | ⟨fml1⟩ | ⟨fml1L, fml1R⟩
  <;> rcases fml2 with _ | ⟨ap2⟩ | ⟨fml2⟩ | ⟨fml2L, fml2R⟩
  <;> try simp [formulaOfLeft] at lm1
  · rfl
  · simp
    rewrite [il.atomicPropOfLeft_injective.eq_iff] at lm1
    exact lm1
  · simp
    exact il.formulaOfLeft_injective lm1
  · simp
    rcases lm1 with ⟨lm1, lm2⟩
    refine ⟨?_, ?_⟩
    · exact il.formulaOfLeft_injective lm1
    · exact il.formulaOfLeft_injective lm2

theorem formulaOfRight_injective (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Function.Injective (il.formulaOfRight) := by
  rintro fml1 fml2 lm1
  rcases fml1 with _ | ⟨ap1⟩ | ⟨fml1⟩ | ⟨fml1L, fml1R⟩
  <;> rcases fml2 with _ | ⟨ap2⟩ | ⟨fml2⟩ | ⟨fml2L, fml2R⟩
  <;> try simp [formulaOfRight] at lm1
  · rfl
  · simp
    rewrite [il.atomicPropOfRight_injective.eq_iff] at lm1
    exact lm1
  · simp
    exact il.formulaOfRight_injective lm1
  · simp
    rcases lm1 with ⟨lm1, lm2⟩
    refine ⟨?_, ?_⟩
    · exact il.formulaOfRight_injective lm1
    · exact il.formulaOfRight_injective lm2



def condOfLeft (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (cond: Cond ECL VarL ValL ValSL) : Cond (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  formula := il.formulaOfLeft cond.formula
  valid := il.formulaOfLeft_isCond_of_isCond cond.valid

def condOfRight (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (cond: Cond ECR VarR ValR ValSR) : Cond (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  formula := il.formulaOfRight cond.formula
  valid := il.formulaOfRight_isCond_of_isCond cond.valid

theorem condOfLeft_injective (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Function.Injective (il.condOfLeft) := by
  intro c1 c2 lm1
  simp [condOfLeft] at lm1
  rewrite [il.formulaOfLeft_injective.eq_iff] at lm1
  exact Cond.ext lm1

theorem condOfRight_injective (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Function.Injective (il.condOfRight) := by
  intro c1 c2 lm1
  simp [condOfRight] at lm1
  rewrite [il.formulaOfRight_injective.eq_iff] at lm1
  exact Cond.ext lm1

@[defeq, pl_simp]
theorem condOfLeft_formula_def {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {cond: Cond ECL VarL ValL ValSL}
  : (il.condOfLeft cond).formula = il.formulaOfLeft cond.formula := rfl

@[defeq, pl_simp]
theorem condOfRight_formula_def {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {cond: Cond ECR VarR ValR ValSR}
  : (il.condOfRight cond).formula = il.formulaOfRight cond.formula := rfl


variable {CCL CCR: Type*} [FiniteCondLike CCL ECL VarL ValL ValSL] [FiniteCondLike CCR ECR VarR ValR ValSR]

variable (CCL CCR) in
def CondHEq (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (condL: CCL) (condR: CCR) : Prop :=
  il.condOfLeft (FiniteCondLike.toCond condL) = il.condOfRight (FiniteCondLike.toCond condR)

@[defeq]
theorem condHEq_def {il: EvalEquiv ECL VarL ValL ECR VarR ValR} {condL: CCL} {condR: CCR}
  : il.CondHEq CCL CCR condL condR = (il.condOfLeft (FiniteCondLike.toCond condL) = il.condOfRight (FiniteCondLike.toCond condR)) :=
  rfl

theorem condHEq_leftUnique (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Relator.LeftUnique (il.CondHEq CCL CCR) := by
  intro cl1 cl2 cr lm1 lm2
  dsimp [condHEq_def] at lm1 lm2
  have lm3 := lm1.trans lm2.symm
  rewrite [il.condOfLeft_injective.eq_iff, FiniteCondLike.toCond_Injective.eq_iff] at lm3
  exact lm3

theorem condHEq_rightUnique (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Relator.RightUnique (il.CondHEq CCL CCR) := by
  intro cl cr1 cr2 lm1 lm2
  dsimp [condHEq_def] at lm1 lm2
  have lm3 := lm1.symm.trans lm2
  rewrite [il.condOfRight_injective.eq_iff, FiniteCondLike.toCond_Injective.eq_iff] at lm3
  exact lm3

instance condHEq_isBiUnique (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : IsBiUnique (il.CondHEq CCL CCR) where
  biUnique := ⟨il.condHEq_leftUnique, il.condHEq_rightUnique⟩


instance decidableCondHEq (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : DecidableRel (il.CondHEq CCL CCR) := fun _ _ => decidable_of_decidable_of_eq condHEq_def.symm

variable (CCL CCR) in
abbrev CondUnion (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Type _ := SumUnion (il.CondHEq CCL CCR)

@[defeq]
theorem condUnion_def {il: EvalEquiv ECL VarL ValL ECR VarR ValR} : il.CondUnion CCL CCR = SumUnion (il.CondHEq CCL CCR) := rfl


namespace CondUnion


instance (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : DecidableEq (il.CondUnion CCL CCR) :=
  letI : DecidableEq CCL := FiniteCondLike.decidableCondLikeEq CCL ECL VarL ValL ValSL
  letI : DecidableEq CCR := FiniteCondLike.decidableCondLikeEq CCR ECR VarR ValR ValSR
  inferInstanceAs (DecidableEq (SumUnion (il.CondHEq CCL CCR)))

instance (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : Fintype (il.CondUnion CCL CCR) :=
  letI : DecidableEq CCL := FiniteCondLike.decidableCondLikeEq CCL ECL VarL ValL ValSL
  letI : DecidableEq CCR := FiniteCondLike.decidableCondLikeEq CCR ECR VarR ValR ValSR
  SumUnion.fintype (il.CondHEq CCL CCR)


variable {il: EvalEquiv ECL VarL ValL ECR VarR ValR}

def toCond (cu: il.CondUnion CCL CCR) : Cond (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) :=
  (cu: SumUnion (il.CondHEq CCL CCR)).funElim (fun condL => il.condOfLeft (FiniteCondLike.toCond condL)) (fun condR => il.condOfRight (FiniteCondLike.toCond condR)) (by
    intro _ _ lm1
    exact lm1 )

open SumUnion in
theorem toCond_Injective : Function.Injective (toCond: il.CondUnion CCL CCR → _) := by
  intro cu1 cu2 lm1
  dsimp [toCond] at lm1
  cases cu1 using indInlInrOfSum
  <;> cases cu2 using indInlInrOfSum
  <;> simp [sum_simp, funElim_eq_ofSum] at ⊢ lm1
  · rewrite [il.condOfLeft_injective.eq_iff, FiniteCondLike.toCond_Injective.eq_iff] at lm1
    exact lm1
  · exact lm1
  · exact lm1.symm
  · rewrite [il.condOfRight_injective.eq_iff, FiniteCondLike.toCond_Injective.eq_iff] at lm1
    exact lm1

@[defeq, pl_simp]
theorem inl_toCond_def {condL: CCL} : toCond (.ofSum (.inl condL): il.CondUnion CCL CCR) = il.condOfLeft (FiniteCondLike.toCond condL) := by
  dsimp [toCond, SumUnion.funElim_eq_ofSum]

@[defeq, pl_simp]
theorem inr_toCond_def {condR: CCR} : toCond (.ofSum (.inr condR): il.CondUnion CCL CCR) = il.condOfRight (FiniteCondLike.toCond condR) := by
  dsimp [toCond, SumUnion.funElim_eq_ofSum]

inductive ControlUnion {Loc1 Loc2 Act1 Act2: Type*}
  (ctr1: Loc1 → CCL → Act1 → Loc1 → Prop) (ctr2: Loc2 → CCR → Act2 → Loc2 → Prop) (loc1: Loc1) (loc2: Loc2) : Loc1 → Loc2 → (il.CondUnion CCL CCR) → (Act1 ⊕ Act2) → Prop where
  | left (loc: Loc1) (cond: CCL) (act: Act1) (req: ctr1 loc1 cond act loc) : ControlUnion ctr1 ctr2 loc1 loc2 loc loc2 (.ofSum (.inl cond)) (.inl act)
  | right (loc: Loc2) (cond: CCR) (act: Act2) (req: ctr2 loc2 cond act loc) : ControlUnion ctr1 ctr2 loc1 loc2 loc1 loc (.ofSum (.inr cond)) (.inr act)


end CondUnion


protected instance finiteCondLike (il: EvalEquiv ECL VarL ValL ECR VarR ValR) : FiniteCondLike (il.CondUnion CCL CCR) (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  toCond cu := cu.toCond
  toCond_Injective := CondUnion.toCond_Injective
  fintype := inferInstance

--ctr : pgL.Loc × pgR.Loc → CondUnion CCL CCR il → pgL.Act ⊕ pgR.Act → pgL.Loc × pgR.Loc → Prop


@[reducible]
def toProgramGraph (il: EvalEquiv ECL VarL ValL ECR VarR ValR) (pgL: ProgramGraph CCL ECL VarL ValL ValSL) (pgR: ProgramGraph CCR ECR VarR ValR ValSR) : ProgramGraph (il.CondUnion CCL CCR) (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  Loc := pgL.Loc × pgR.Loc
  Act := pgL.Act ⊕ pgR.Act
  effect := il.mergeEffect pgL.effect pgR.effect
  ctr l cu act l' := CondUnion.ControlUnion pgL.ctr pgR.ctr l.fst l.snd l'.fst l'.snd cu act
  loc0 l := pgL.loc0 l.fst ∧ pgR.loc0 l.snd
  g0 := (il.condOfLeft pgL.g0).append (il.condOfRight pgR.g0)


end StandardTypeConcreteFinite

end EvalEquiv


--def areFormularHEq


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
