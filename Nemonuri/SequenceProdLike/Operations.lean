module

public import Nemonuri.SequenceProdLike.Basic
public import Nemonuri.SequenceProd.Operations

@[expose] public section

namespace Nemonuri.SequenceProdLike

open SequenceProd

structure SingleFstOp (C α β: Type _) [SequenceProdLike C α β] where
  singleFstBy : α → C
  getAt?_zero {a: α} : toGetAt? (singleFstBy a) 0 = OptionProd.fst a
  getAt?_add_one {a: α} {i: ℕ} : toGetAt? (singleFstBy a) (i+1) = OptionProd.none

namespace SingleFstOp

variable {C α β: Type _} [SequenceProdLike C α β]
         {sfo: SingleFstOp C α β} {a: α}

theorem getAt?_zero_at (a: α) : toGetAt? (sfo.singleFstBy a) 0 = OptionProd.fst a := sfo.getAt?_zero

theorem getAt?_add_one_at (a: α) (i: ℕ) : toGetAt? (sfo.singleFstBy a) (i+1) = OptionProd.none := sfo.getAt?_add_one



theorem singleFstBy_singleFst
  : (toSequenceProd ∘ sfo.singleFstBy) = singleFst α β := by
  refine funext ?_
  intro a
  dsimp
  refine SequenceProd.getAt?_ext ?_
  refine funext ?_
  intro i
  induction i with
  | zero =>
    have lm1 := sfo.getAt?_zero_at a
    rewrite [toGetAt?_eq_toSequenceProd_getAt?] at lm1
    rw [lm1]
    rw [singleFst_getAt?_zero]
  | succ i lm1 =>
    have lm2 := sfo.getAt?_add_one_at a i
    rewrite [toGetAt?_eq_toSequenceProd_getAt?] at lm2
    rw [lm2]
    rw [singleFst_getAt?_add_one]

end SingleFstOp


structure StepLOp (C α β: Type _) [SequenceProdLike C α β] where
  stepLBy : α → β → C → C
  getAt?_zero {a: α} {b: β} {sp: C} : toGetAt? (stepLBy a b sp) 0 = OptionProd.both a b
  getAt?_add_one {a: α} {b: β} {sp: C} {i: ℕ} : toGetAt? (stepLBy a b sp) (i+1) = toGetAt? sp i

namespace StepLOp

variable {C α β: Type _} [SequenceProdLike C α β]
         {slo: StepLOp C α β} {a: α} {b: β} {sp: C}

theorem getAt?_zero_at (a: α) (b: β) (sp: C) : toGetAt? (slo.stepLBy a b sp) 0 = OptionProd.both a b := slo.getAt?_zero

theorem getAt?_add_one_at (a: α) (b: β) (sp: C) (i: ℕ) : toGetAt? (slo.stepLBy a b sp) (i+1) = toGetAt? sp i := slo.getAt?_add_one

theorem stepLBy_stepL : (fun a b => toSequenceProd ∘ (slo.stepLBy a b)) = (fun a b => (stepL a b) ∘ toSequenceProd) := by
  ext a b sp
  dsimp
  have lm1 := slo.getAt?_zero_at a b sp
  have lm2 := slo.getAt?_add_one_at a b sp
  simp only [toGetAt?_eq_toSequenceProd_getAt?] at lm1 lm2
  refine SequenceProd.getAt?_ext ?_
  ext i
  induction i with
  | zero =>
    rw [lm1]
    rw [stepL_getAt?_zero]
  | succ i lm3 =>
    specialize lm2 i
    rw [lm2]
    rw [stepL_getAt?_add_one_at]



end StepLOp


end Nemonuri.SequenceProdLike

end
