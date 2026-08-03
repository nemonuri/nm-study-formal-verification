module

public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence

@[expose] public section

namespace Nemonuri.TransitionSystem

open Cslib

structure InfiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states : ωSequence ts.S
  actions : ωSequence ts.Act

namespace InfiniteExecutionFragmentRaw

variable {ts: TransitionSystem}

def ofListRepeat (states: List ts.S) (actions: List ts.Act) (req1: states ≠ []) (req2: actions ≠ []) : ts.InfiniteExecutionFragmentRaw :=
  ⟨.ofListRepeat states req1, .ofListRepeat actions req2⟩



end InfiniteExecutionFragmentRaw

end Nemonuri.TransitionSystem

end
