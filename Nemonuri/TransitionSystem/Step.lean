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


namespace StepR

variable {ts: TransitionSystem}

theorem nonempty_of_not_terminal (pre: ts.S) (req: ¬ts.IsTerminal pre) : Nonempty (ts.StepR pre) := by
  simp [isTerminal_iff] at req
  rcases req with ⟨act, post, lm1⟩
  exact .intro ⟨⟨act, post⟩, lm1⟩

theorem empty_of_termial (pre: ts.S) (req: ts.IsTerminal pre) : IsEmpty (ts.StepR pre) where
  false x := by
    rcases x with ⟨s, lm1⟩
    simp [isTerminal_iff] at req
    exact req _ _ lm1

theorem nonempty_iff_not_terminal (pre: ts.S) : Nonempty (ts.StepR pre) ↔ (¬ts.IsTerminal pre) := by
  constructor
  · intro lm1 lm2
    have lm3 := empty_of_termial _ lm2
    revert lm3
    simp
  · exact nonempty_of_not_terminal pre

end StepR


end Nemonuri.TransitionSystem

end
