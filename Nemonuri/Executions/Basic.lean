module

public import Nemonuri.SequenceProd.Basic
public import Nemonuri.SequenceProd.IsWShape
public import Nemonuri.TransitionSystem

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1.1 Executions, p.24

-/


@[expose] public section

/-!

### Definition 2.6. Execution Fragment

-/

namespace Nemonuri.TransitionSystem

open SequenceProd

structure IsExecutionFragment {ts: TransitionSystem} (sp: SequenceProd ts.S ts.Act) : Prop where
  wShape : IsWShape sp
  lts_tr (i: ℕ) (req: i < sp.snd.length?) : (sp.fst.getAt i (wShape.lt_fst_length?_of_lt_snd_length? req)) ─⌞(sp.snd.getAt i req)⌟→{ts} (sp.fst.getAt (i+1) (wShape.add_one_lt_fst_length?_of_lt_snd_length? req))



variable {ts: TransitionSystem}

/-!

### Definition 2.7. Maximal and Initial Execution Fragment

-/

/-- A *maximal* execution fragment is either a finite execution fragment that
ends in a terminal state, or an infinite execution fragment. -/
structure IsMaximal (sp: SequenceProd ts.S ts.Act) : Prop where
  executionFragment: IsExecutionFragment sp
  terminal (s: ts.S) (req: s ∈ sp.fst.last?) : ts.IsTerminal s

/-- An execution fragment is called initial if it starts in an initial state -/
structure IsInitial (sp: SequenceProd ts.S ts.Act) : Prop where
  executionFragment: IsExecutionFragment sp
  mem_i: sp.fst.head (executionFragment.wShape.fst_nonempty) ∈ ts.I

namespace IsExecutionFragment

variable {sp: SequenceProd ts.S ts.Act}

theorem maximal_of_infinite (h: ts.IsExecutionFragment sp) (req: sp.toFiniteLabel h.wShape.finite_eq = .infinite) : ts.IsMaximal sp := by
  refine .mk h ?_
  simp only [Option.mem_def]
  intro s lm1
  rewrite [Sequence.last?_eq_getFromLastAt?_zero, Sequence.getFromLastAt?_eq_some_iff_getAt?_eq_some] at lm1
  rcases lm1 with ⟨lm1, _⟩
  rewrite [← sp.fst_self_finiteEq] at req
  simp [lm1] at req



end IsExecutionFragment




end Nemonuri.TransitionSystem

end
