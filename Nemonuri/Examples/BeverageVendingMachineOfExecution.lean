module


public import Nemonuri.Examples.BeverageVendingMachine
public import Nemonuri.Executions.ExecutionFragment.Expr
public import Nemonuri.Executions.ExecutionFragment.Maximal

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.8. Executions of the Beverage Vending Machine, p.25

-/


@[expose] public section

namespace Examples.Executions

open Nemonuri TransitionSystem
open Cslib ωSequence
open ExecutionFragment Expr


def ρ₁ := 𝐸𝑥𝑒𝑐{ts}⸨ &(.pay) ─⌞.insert_coin⌟→ &(.select) ─⌞.τ⌟→ &(.soda) ─⌞.get_soda⌟→ &(.pay)
                    ─⌞.insert_coin⌟→ &(.select) ─⌞.τ⌟→ &(.soda) ─⌞.get_soda⌟→ ... ⸩

def ρ₂ := 𝐸𝑥𝑒𝑐{ts}⸨ &(.select)─⌞.τ⌟→ &(.soda)─⌞.get_soda⌟→ &(.pay)─⌞.insert_coin⌟→ &(.select)─⌞.τ⌟→ &(.beer)─⌞.get_beer⌟→ ...⸩

def ϱ := 𝐸𝑥𝑒𝑐{ts}⸨ &(.pay) ─⌞.insert_coin⌟→ &(.select)─⌞.τ⌟→ &(.soda)─⌞.get_soda⌟→ &(.pay)
                    ─⌞.insert_coin⌟→ &(.select)─⌞.τ⌟→ State.soda ⸩


/-! Execution fragments `ρ₁` and `ϱ` are initial, but `ρ₂` is not. -/

theorem ρ₁_initial (x: ρ₁) : (x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x
  simp only [Subtype.forall]
  intro x lm1
  dsimp [ρ₁] at lm1
  simp only [ExprRaw.EvalToSet.mem_iff_mem] at lm1
  refine lm1.isInitial_iff.mpr ?_
  rcases x with ϱ | ρ
  · refine absurd lm1 ?_
    refine ExprRaw.Mem.not_finite_infinite ?_ ?_
    · dsimp
    · conv => lhs; change (@HasLabel.toLabel Sequence.Label _ _ (ExprRaw ts) _ _)
      simp only [ExprRaw.stepL_eq_stepL', ExprRaw.stepL'_preserves_seqLabel, HasLabel.Preserves.cancel]
      rfl
  · have lm2 req := @lm1.pre_is_prefix.states_getElem_eq _ _ _ 0 req |> Eq.symm
    simpa using lm2


theorem ϱ_initial (x: ϱ) : (x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x; simp only [Subtype.forall]; intro x lm1
  dsimp [ϱ] at lm1;
  simp only [ExprRaw.EvalToSet.mem_iff_mem] at lm1
  refine lm1.isInitial_iff.mpr ?_
  rcases x with ϱ | ρ
  · have lm2 req := @lm1.pre_is_prefix.states_getElem_eq _ _ _ 0 req |> Eq.symm
    simpa using lm2
  · refine absurd lm1 ?_
    refine ExprRaw.Mem.not_infinite_finite ?_ ?_
    · dsimp
    · conv => lhs; change (@HasLabel.toLabel Sequence.Label _ _ (ExprRaw ts) _ _)
      simp only [ExprRaw.stepL_eq_stepL', ExprRaw.stepL'_preserves_seqLabel, HasLabel.Preserves.cancel]
      rfl

theorem not_ρ₂_initial (x: ρ₂) : ¬(x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x; simp only [Subtype.forall]; intro x lm1
  dsimp [ρ₂] at lm1
  simp only [ExprRaw.EvalToSet.mem_iff_mem] at lm1
  refine lm1.isInitial_iff.not.mpr ?_
  have lm2 req := @lm1.pre_is_prefix.states_getElem_eq _ _ _ 0 req
  simp at lm2
  intro cont; simp at cont
  have lm3 := Eq.trans lm2 cont
  simp at lm3






end Examples.Executions

end
