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
structure AreEvalEquiv (il: Interleaving VarL ValL VarR ValR) : Prop where
  right_exists (ecl: ECL) : ∃(ecr: ECR), FunHEq il.var.Rel il.val.Rel ↑ecl ↑ecr
  left_exists (ecr: ECR) : ∃(ecl: ECL), FunHEq il.var.Rel il.val.Rel ↑ecl ↑ecr

namespace AreEvalEquiv

variable {il: Interleaving VarL ValL VarR ValR} {stL: StandardType ECL VarL ValL ValSL} {stR: StandardType ECR VarR ValR ValSR}

variable (stL stR) in
theorem areTypeEquiv (h: il.AreEvalEquiv ECL ECR) : il.AreTypeEquiv stL.toStruct stR.toStruct := by
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

theorem left_to_right_choice_exists (h: il.AreEvalEquiv ECL ECR) : ∃(f: ECL → ECR), ∀(ecL: ECL), FunHEq il.var.Rel il.val.Rel ecL (f ecL) :=
  Classical.axiomOfChoice h.right_exists

theorem right_to_left_choice_exists (h: il.AreEvalEquiv ECL ECR) : ∃(f: ECR → ECL), ∀(ecR: ECR), FunHEq il.var.Rel il.val.Rel (f ecR) ecR :=
  Classical.axiomOfChoice h.left_exists

theorem of_choice₂ (flr: ECL → ECR) (req1: ∀(ecL: ECL), FunHEq il.var.Rel il.val.Rel ecL (flr ecL)) (frl: ECR → ECL) (req2: ∀(ecR: ECR), FunHEq il.var.Rel il.val.Rel (frl ecR) ecR)
  : il.AreEvalEquiv ECL ECR := by
  refine .mk ?_ ?_
  · intro ecL
    specialize req1 ecL
    exists (flr ecL)
  · intro ecR
    specialize req2 ecR
    exists (frl ecR)

end AreEvalEquiv

theorem areEvalEquiv_iff_skolem {il: Interleaving VarL ValL VarR ValR}
  : (il.AreEvalEquiv ECL ECR) ↔ (∃(flr: ECL → ECR) (frl: ECR → ECL), ∀(ecL: ECL) (ecR: ECR), FunHEq il.var.Rel il.val.Rel ecL (flr ecL) ∧ FunHEq il.var.Rel il.val.Rel (frl ecR) ecR) := by
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
    refine AreEvalEquiv.of_choice₂ flr ?_ frl ?_
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
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR) (req1: il.AreEvalEquiv ECL ECR)
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

def toStandardType (il: Interleaving VarL ValL VarR ValR) (req: il.AreEvalEquiv ECL ECR)
  (stL: StandardType ECL VarL ValL ValSL) (stR: StandardType ECR VarR ValR ValSR)
  : StandardType (il.EvalInter ECL ECR) (SumUnion il.var.Rel) (SumUnion il.val.Rel) (SetLikeUnion il.val.Rel ValSL ValSR) where
  toStruct := il.toStandardTypeStruct (req.areTypeEquiv stL stR)
  valid := {
    type_safe := il.toStandardTypeStruct_type_safe stL stR (req.areTypeEquiv stL stR)
    eval_exists := il.toStandardTypeStruct_eval_exists stL stR req
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
