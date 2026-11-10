module


public import Nemonuri.TransitionSystem.Deterministic


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

structure StepStruct (ts: TransitionSystem) where
  pre: ts.S
  act: ts.Act
  post: ts.S

structure Step (ts: TransitionSystem) extends toStruct: ts.StepStruct where
  valid: toStruct.pre ─⌞ toStruct.act ⌟→{ ts } toStruct.post

structure StepRStruct (ts: TransitionSystem) where
  act: ts.Act
  post: ts.S

structure StepR (ts: TransitionSystem) (pre: ts.S) extends toStruct: ts.StepRStruct where
  valid: pre ─⌞ toStruct.act ⌟→{ ts } toStruct.post

end Nemonuri.TransitionSystem

end
