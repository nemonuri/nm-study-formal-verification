module

public import Nemonuri.TransitionSystemLike.Basic
--public import Nemonuri.PropositionalLogics

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 32

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.ProgramGraph


structure Eval (Var Val: Type*) where
  eval: Var → Val

instance {Var Val: Type*} : FunLike (Eval Var Val) Var Val where
  coe ev := ev.eval
  coe_injective := by rintro ⟨_⟩ ⟨_⟩; simp


class EvalLike (EC: Type*) (Var Val: outParam Type*) where
  protected coe: EC → Eval Var Val
  coe_injective: Function.Injective coe

attribute [coe, reducible] EvalLike.coe

namespace EvalLike

variable {EC Var Val: Type*} [EvalLike EC Var Val]

instance : CoeOut EC (Eval Var Val) := ⟨EvalLike.coe⟩

instance : FunLike EC Var Val where
  coe ec := (ec: Eval Var Val)
  coe_injective := DFunLike.coe_injective.comp EvalLike.coe_injective

@[defeq]
theorem coe_coe_eq_coe {ec: EC} : ((ec: Eval Var Val): Var → Val) = (ec: Var → Val) := rfl


variable (EC Var Val) in
structure UpdateOPStructure where
  op: Var → Val → EC → EC

open Classical in
structure IsUpdateOP (s: UpdateOPStructure EC Var Val) : Prop where
  update_eq (var: Var) (val: Val) (ec: EC) : Function.update (↑ec) var val = ↑(s.op var val ec)

variable (EC Var Val) in
structure UpdateOP extends toStruct: UpdateOPStructure EC Var Val where
  valid: IsUpdateOP toStruct

namespace UpdateOP


instance subsingleton : Subsingleton (UpdateOP EC Var Val) where
  allEq := by
    rintro ⟨⟨op1⟩, ⟨lm1⟩⟩ ⟨⟨op2⟩, ⟨lm2⟩⟩
    simp [funext_iff]
    simp at lm1 lm2
    intro var val ec
    specialize lm1 var val ec
    specialize lm2 var val ec
    have lm3 := lm1.symm.trans lm2
    exact DFunLike.coe_injective.eq_iff.mp lm3

theorem op_idem (upd: UpdateOP EC Var Val) (var: Var) (val1 val2: Val) (ec: EC)
  : upd.op var val2 (upd.op var val1 ec) = upd.op var val2 ec := by
  have lm1 := upd.valid.update_eq var
  refine DFunLike.coe_injective.eq_iff.mp ?_
  simp only [← lm1]
  simp only [Function.update_idem]

open Classical in
theorem op_apply (upd: UpdateOP EC Var Val) (var': Var) (val: Val) (ec: EC) (var: Var)
  : (upd.op var' val ec) var = if var = var' then val else ec var := by
  rewrite [← upd.valid.update_eq, Function.update_apply]
  rfl

theorem op_eq_self_iff (upd: UpdateOP EC Var Val) (ec: EC) (var: Var) (val: Val)
  : (ec = upd.op var val ec) ↔ (ec var = val) := by
  classical
  conv => lhs; rw [← DFunLike.coe_injective.eq_iff, ← upd.valid.update_eq, Function.eq_update_self_iff]

theorem op_eq_self (upd: UpdateOP EC Var Val) (ec: EC) (var: Var)
  : upd.op var (ec var) ec = ec := by
  classical
  refine DFunLike.coe_injective.eq_iff.mp ?_
  rw [← upd.valid.update_eq]
  exact Function.update_eq_self _ _

theorem op_apply_eq_of_ne (upd: UpdateOP EC Var Val) (ec: EC) (val: Val) {var var': Var} (req: var ≠ var')
  : (upd.op var' val ec) var = ec var := by
  simp [upd.op_apply, req]

theorem op_comm (upd: UpdateOP EC Var Val) (ec: EC) {var1 var2: Var} (req1: var1 ≠ var2) (val1 val2: Val)
  : upd.op var1 val1 (upd.op var2 val2 ec) = upd.op var2 val2 (upd.op var1 val1 ec) := by
  classical
  refine DFunLike.coe_injective.eq_iff.mp ?_
  simp [← upd.valid.update_eq]
  symm
  exact Function.update_comm req1 _ _ _


def updateIfSome (upd: UpdateOP EC Var Val) (var: Var) (val?: Option Val) (ec: EC) : EC :=
  match val? with
  | .none => ec
  | .some val => upd.op var val ec

def updateOfPFun (upd: UpdateOP EC Var Val) (pf: Var → Option Val) (var: Var) (ec: EC) : EC := upd.updateIfSome var (pf var) ec

def updateAllOfPFun (upd: UpdateOP EC Var Val) (pf: Var → Option Val) : List Var → EC → EC
  | [] => id
  | var::vars => (fun ec =>
      let ecNext : EC := upd.updateOfPFun pf var ec
      upd.updateAllOfPFun pf vars ecNext)


theorem updateAllOfPFun_apply_eq_of_not_mem (upd: UpdateOP EC Var Val) (pf: Var → Option Val) (var: Var) (vars: List Var) (req: var ∉ vars) (ec: EC)
  : (upd.updateAllOfPFun pf vars ec) var = ec var := by
  cases vars with
  | nil => dsimp [updateAllOfPFun]
  | cons var2 vars =>
    simp at req
    rcases req with ⟨lm1, lm2⟩
    dsimp [updateAllOfPFun, updateOfPFun]
    generalize pf var2 = val?
    rcases val? with _ | val
    · dsimp [updateIfSome]
      exact upd.updateAllOfPFun_apply_eq_of_not_mem pf var vars lm2 ec
    · dsimp [updateIfSome]
      have lm3:= upd.updateAllOfPFun_apply_eq_of_not_mem pf var vars lm2 (upd.op var2 val ec)
      refine Eq.trans lm3 ?_
      exact upd.op_apply_eq_of_ne _ _ lm1



theorem updateAllOfPFun_swap_eq (upd: UpdateOP EC Var Val) (pf: Var → Option Val) (var1 var2: Var) (vars: List Var)
  : upd.updateAllOfPFun pf (var1 :: var2 :: vars) = upd.updateAllOfPFun pf (var2 :: var1 :: vars) := by
  refine funext ?_
  intro ec
  by_cases lm1: var1 = var2
  · subst lm1; rfl
  · dsimp [updateAllOfPFun, updateOfPFun]
    generalize lm2: pf var1 = val1?
    generalize lm3: pf var2 = val2?
    rcases val1? with _ | val1
    <;> rcases val2? with _ | val2
    <;> dsimp [updateIfSome]
    · rw [← (upd.op_comm ec lm1 val1 val2)]


theorem updateAllOfPFun_cons_apply_eq_of_mem (upd: UpdateOP EC Var Val) (pf: Var → Option Val) (var: Var) (vars: List Var) (req: var ∈ vars) (ec: EC)
  : (upd.updateAllOfPFun pf (var :: vars) ec) = (upd.updateAllOfPFun pf vars ec) := by
  cases vars with
  | nil => simp at req
  | cons var2 vars =>
    simp at req
    rcases req with lm1 | lm1
    · subst lm1
      dsimp [updateAllOfPFun, updateOfPFun]
      generalize pf var = val?
      rcases val? with _ | val
      · dsimp [updateIfSome]
      · dsimp [updateIfSome]
        conv => lhs; arg 4; rw [upd.op_idem]
    · dsimp [updateAllOfPFun, updateOfPFun]
      generalize lm2: pf var = val?
      generalize lm3: pf var2 = val2?
      rcases val? with _ | val
      <;> rcases val2? with _ | val2
      <;> dsimp [updateIfSome]
      · have lm4 := upd.updateAllOfPFun_cons_apply_eq_of_mem pf var vars lm1 ec
        dsimp [updateAllOfPFun, updateOfPFun] at lm4
        simp [lm2] at lm4
        dsimp [updateIfSome] at lm4
        exact lm4
      · by_cases lm4: var = var2
        · subst lm4
          rw [upd.op_idem]
        · rw [← (upd.op_comm ec lm4 val val2)]
          have lm5 := upd.updateAllOfPFun_cons_apply_eq_of_mem pf var vars lm1 (upd.op var2 val2 ec)
          dsimp [updateAllOfPFun, updateOfPFun] at lm5
          simp [lm2] at lm5
          dsimp [updateIfSome] at lm5
          exact lm5


theorem updateAllOfPFun_eq_apply_of_mem_and_eq_some (upd: UpdateOP EC Var Val)
  (pf: Var → Option Val) (var: Var) (vars: List Var) (req1: var ∈ vars) (val: Val) (req2: pf var = .some val) (ec: EC)
  : (upd.updateAllOfPFun pf vars ec) var = val := by
  cases vars with
  | nil => simp at req1
  | cons var2 vars =>
    simp at req1
    rcases req1 with lm1 | lm1
    · subst lm1
      by_cases lm1: var ∈ vars
      · have lm2 := upd.updateAllOfPFun_cons_apply_eq_of_mem pf var vars lm1 ec
        rewrite [DFunLike.ext_iff] at lm2
        specialize lm2 var
        refine Eq.trans lm2 ?_
        exact upd.updateAllOfPFun_eq_apply_of_mem_and_eq_some pf var vars lm1 val req2 ec
      · have lm2 := upd.updateAllOfPFun_apply_eq_of_not_mem pf var vars lm1
        dsimp [updateAllOfPFun, updateOfPFun]
        simp [req2]
        dsimp [updateIfSome]
        specialize lm2 (upd.op var val ec)
        refine Eq.trans lm2 ?_
        simp [upd.op_apply]
    · by_cases lm2: var = var2
      · subst lm2
        have lm2 := upd.updateAllOfPFun_cons_apply_eq_of_mem pf var vars lm1 ec
        rw [lm2]
        exact upd.updateAllOfPFun_eq_apply_of_mem_and_eq_some pf var vars lm1 val req2 ec
      · dsimp [updateAllOfPFun, updateOfPFun]
        exact upd.updateAllOfPFun_eq_apply_of_mem_and_eq_some pf var vars lm1 val req2 _

theorem updateAllOfPFun_eq_apply_of_eq_none (upd: UpdateOP EC Var Val) (pf: Var → Option Val) (var: Var) (req: pf var = .none) (vars: List Var) (ec: EC)
  : (upd.updateAllOfPFun pf vars ec) var = ec var := by
  cases vars with
  | nil => dsimp [updateAllOfPFun]
  | cons var2 vars =>
    dsimp [updateAllOfPFun, updateOfPFun]
    generalize lm1: pf var2 = val?
    rcases val? with _ | val
    · dsimp [updateIfSome]
      exact upd.updateAllOfPFun_eq_apply_of_eq_none pf var req vars ec
    · dsimp [updateIfSome]
      have lm2 := upd.updateAllOfPFun_eq_apply_of_eq_none pf var req vars (upd.op var2 val ec)
      refine Eq.trans lm2 ?_
      have lm3 : var ≠ var2 := by intro lm3; subst lm3; simp [req] at lm1
      exact upd.op_apply_eq_of_ne ec val lm3


theorem updateAllOfPFun_respects_perm (upd: UpdateOP EC Var Val) (pf: Var → Option Val) (vs1 vs2: List Var) (req: vs1.Perm vs2) : upd.updateAllOfPFun pf vs1 = upd.updateAllOfPFun pf vs2 := by
  induction req with
  | nil => rfl
  | @cons v vs1 vs2 lm1 lm2 =>
    simp [funext_iff] at ⊢ lm2
    intro ec
    simp [DFunLike.ext_iff] at ⊢ lm2
    intro v2
    dsimp [updateAllOfPFun]
    specialize lm2 (upd.updateOfPFun pf v ec) v2
    exact lm2
  | swap v1 v2 vs => exact upd.updateAllOfPFun_swap_eq pf v2 v1 vs
  | trans _ _ lm1 lm2 => exact lm1.trans lm2



end UpdateOP

variable (EC Var Val) in
class HasUpdateOP where
  updateOP: UpdateOP EC Var Val

namespace HasUpdateOP



end HasUpdateOP


end EvalLike


end Nemonuri.ProgramGraph

end
