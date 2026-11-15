module

public import Nemonuri.TransitionSystem.Executor
public import Nemonuri.Relations.Heterogeneous.SumRelGen

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 38

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

open Nemonuri.Relations.Heterogeneous

structure InterleaverStruct (ts1 ts2: TransitionSystem) where
  areActHEq: ts1.Act → ts2.Act → Bool
  areApHEq: ts1.AP → ts2.AP → Bool

structure IsInterleaver {ts1 ts2: TransitionSystem} (s: InterleaverStruct ts1 ts2) : Prop where
  areActHEq_biUnique: Relator.BiUnique (s.areActHEq · · = .true)
  areApHEq_biUnique: Relator.BiUnique (s.areApHEq · · = .true)


end Nemonuri.TransitionSystem

end
