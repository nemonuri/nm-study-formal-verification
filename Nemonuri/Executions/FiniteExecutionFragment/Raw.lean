module

public import Nemonuri.TransitionSystem
public import Nemonuri.Sequence

@[expose] public section

namespace Nemonuri.TransitionSystem

structure FiniteExecutionFragmentRaw (ts: TransitionSystem) where
  states: List ts.S
  actions: List ts.Act



end Nemonuri.TransitionSystem

end
