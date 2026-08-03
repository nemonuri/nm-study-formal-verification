module


public import Nemonuri.Examples.BeverageVendingMachine
public import Nemonuri.Executions.ExecutionFragment.Expr

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

/-
theorem ρ₁_nonempty : ρ₁.Nonempty := by
  rw [Set.nonempty_def]
-/
  --dsimp [ρ₁]
  --dsimp [ExprRaw.EvalToSet]




end Examples.Executions

end
