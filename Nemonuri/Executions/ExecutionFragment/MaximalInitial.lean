module

public import Nemonuri.Executions.ExecutionFragment.Basic


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1.1 Executions, p.24

-/


@[expose] public section

namespace Nemonuri.TransitionSystem

/-!

### Definition 2.7. Maximal and Initial Execution Fragment

-/

namespace ExecutionFragment

variable {ts: TransitionSystem}

/-- A *maximal* execution fragment is either a finite execution fragment that
ends in a terminal state, or an infinite execution fragment. -/
inductive IsMaximal : ts.ExecutionFragment → Prop where
  | finite (ϱ: ts.FiniteExecutionFragment)
           (req: ts.IsTerminal <| ϱ.states.getLast (List.length_pos_iff.mp ϱ.states_length_pos))
           : IsMaximal (.ofFinite ϱ)
  | infinite (ρ: ts.InfiniteExecutionFragment) : IsMaximal (.ofInfinite ρ)

/-- An execution fragment is called initial if it starts in an initial state -/
def IsInitial (ef: ts.ExecutionFragment) : Prop := ef.state0 ∈ ts.I

end ExecutionFragment

end Nemonuri.TransitionSystem

end
