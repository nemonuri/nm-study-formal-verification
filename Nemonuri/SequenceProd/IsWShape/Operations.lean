module

public import Nemonuri.SequenceProd.IsWShape.Basic
public import Nemonuri.SequenceProd.Operations

@[expose] public section

namespace Nemonuri.SequenceProd.IsWShape

variable {α β: Type _}  {sp sp2: SequenceProd α β} {a: α} {b: β}

theorem of_singleFst : (singleFst α β a).IsWShape := by
  refine .mk ?_
  dsimp [singleFst]
  rw [Sequence.single_length?_eq_one, Sequence.nil_length?_eq_zero]
  simp

theorem stepL_iff : (sp.stepL a b).IsWShape ↔ sp.IsWShape := by
  constructor
  · intro lm1
    refine .mk ?_
    have lm2 := lm1.length?_eq
    dsimp [stepL] at lm2
    simp [Sequence.cons_length?_eq_length?_add_one] at lm2
    exact lm2
  · intro lm1
    refine .mk ?_
    have lm2 := lm1.length?_eq
    dsimp [stepL]
    simp [Sequence.cons_length?_eq_length?_add_one]
    exact lm2

theorem not_nil : ¬(nil: SequenceProd α β).IsWShape := by
  intro lm1
  dsimp [nil] at lm1
  replace lm1 := lm1.fst_nonempty
  dsimp at lm1
  simp [Sequence.nil_empty] at lm1

end Nemonuri.SequenceProd.IsWShape

end
