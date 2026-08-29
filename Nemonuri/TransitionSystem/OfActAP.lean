module

public import Nemonuri.TransitionSystem.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem

universe u1 u2 u3

inductive OfActAP : Type u2 → Type u3 → Type _ where
  | mk (ts: TransitionSystem.{u1, u2, u3}) : OfActAP ts.Act ts.AP

abbrev toActAP (ts: TransitionSystem) : OfActAP ts.Act ts.AP := .mk ts


end Nemonuri.TransitionSystem

end
