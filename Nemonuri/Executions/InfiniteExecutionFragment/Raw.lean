module

public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence

@[expose] public section

namespace Nemonuri.TransitionSystem

open Cslib

structure InfiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states : ωSequence ts.S
  actions : ωSequence ts.Act


end Nemonuri.TransitionSystem

end
