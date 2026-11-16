module

public import Nemonuri.TransitionSystem.StepSequence

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 35

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

--structure Parallel where ofList :: toList : List TransitionSystem

structure ParallelOpStruct where
  op: TransitionSystem → TransitionSystem → TransitionSystem

structure IsParallelOp (s: ParallelOpStruct) : Prop where
  assoc: Std.Associative s.op
  comm: Std.Commutative s.op

structure ParallelOp extends toStruct: ParallelOpStruct where
  valid: IsParallelOp toStruct


namespace ParallelOp

instance (pop: ParallelOp) : Std.Associative pop.op := pop.valid.assoc

instance (pop: ParallelOp) : Std.Commutative pop.op := pop.valid.comm

def iterOp (pop: ParallelOp) (ts: TransitionSystem) : List TransitionSystem → TransitionSystem
  | [] => ts
  | ts2::tss => pop.iterOp (pop.op ts ts2) tss

def compose (pop: ParallelOp) (tss: List TransitionSystem) (req: tss ≠ []) : TransitionSystem := pop.iterOp (tss.head req) tss.tail

def decomposeAt (pop: ParallelOp) (ts: TransitionSystem) (i: ℕ)
  (tss: List TransitionSystem) (req1: i < tss.length) (_: pop.compose tss (tss.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le i) req1)) = ts) : TransitionSystem :=
  tss[i]

--(req1: tss ≠ []) (_: pop.compose tss req1 = ts)

end ParallelOp


end Nemonuri.TransitionSystem

end
