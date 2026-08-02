module

public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence

@[expose] public section

namespace Nemonuri.TransitionSystem

structure FiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states: List ts.S
  actions: List ts.Act

namespace FiniteExecutionFragmentRaw

variable {ts: TransitionSystem}

def singleState (s: ts.S) : ts.FiniteExecutionFragmentRaw := ⟨[s], []⟩

def stepL (tail: ts.FiniteExecutionFragmentRaw) (state0: ts.S) (action0: ts.Act) : ts.FiniteExecutionFragmentRaw :=
  ⟨state0 :: tail.states, action0 :: tail.actions⟩


end FiniteExecutionFragmentRaw


end Nemonuri.TransitionSystem

end
