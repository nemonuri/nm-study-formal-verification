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

section Proof1

open ExprRaw

theorem ρ₁_initial (x: ρ₁) : (x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x
  simp [ρ₁, EvalToSet.mem_iff_mem]
  intro x lm1
  simp [lm1.isInitial_iff]
  have lm2 := lm1.pre_is_prefix.states_getElem_eq' 0
  simp at lm2; exact lm2.symm


theorem ϱ_initial (x: ϱ) : (x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x
  simp [ϱ, EvalToSet.mem_iff_mem]
  intro x lm1
  simp [lm1.isInitial_iff]
  have lm2 := lm1.pre_is_prefix.states_getElem_eq' 0
  simp at lm2; exact lm2.symm

theorem not_ρ₂_initial (x: ρ₂) : ¬(x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x; simp only [Subtype.forall]; intro x lm1
  dsimp [ρ₂] at lm1
  simp only [ExprRaw.EvalToSet.mem_iff_mem] at lm1
  refine lm1.isInitial_iff.not.mpr ?_
  have lm2 := lm1.pre_is_prefix.states_getElem_eq' 0
  simp at lm2
  intro cont; simp at cont
  have lm3 := Eq.trans lm2 cont
  simp at lm3

end Proof1



end Examples.Executions

end
