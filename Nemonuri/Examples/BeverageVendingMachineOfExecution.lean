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

#print ExprRaw.Mem.infinite1
#print HasLabel.toLabel

theorem ρ₁_initial (x: ρ₁) : x.val.IsInitial := by
  revert x
  simp only [Subtype.forall]
  intro x lm1
  dsimp [ρ₁] at lm1
  have lm2 := ExprRaw.EvalToSet.mem_imp_isExecutionFragment _ _ lm1
  dsimp [ExecutionFragmentRaw.IsInitial]
  exists lm2
  dsimp [ExecutionFragment.IsInitial]
  simp only [Set.mem_singleton_iff]
  dsimp only [ExecutionFragment.state0, ExecutionFragment.states]
  dsimp [ExprRaw.EvalToSet] at lm1
  cases x
  · refine absurd lm1 ?_
    refine ExprRaw.mem_not_finite_infinite ?_ ?_
    · dsimp
    · simp only [ExprRaw.stepL_eq_stepL']
      conv => lhs; change (HasLabel.toLabel (_: ExprRaw ts): Sequence.Label)
      simp only [ExprRaw.stepL'_preserves_seqLabel, ← HasLabel.Preserves.apply]
      rfl
  · sorry




      --have lm3 s a := HasLabel.LabelHom.coe_mk _ (@ExprRaw.stepL'_preserves_seqLabel ts s a)
      --conv => lhs; arg 1; dsimp [ExprRaw.stepL]




      --have lm3 := HasLabel.LabelHom.coe_mk _ ExprRaw.stepL_preserves_seqLabel

  --have lm1 := x.property
  --have lm2 :=
  --dsimp [ExecutionFragment.IsInitial]
  --simp only [Set.mem_singleton_iff]


end Examples.Executions

end
