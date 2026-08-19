module

public meta import Nemonuri.Executions.Specs.Notation
public import Nemonuri.Examples.BeverageVendingMachine
public import Nemonuri.Executions.Specs.Basic


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], Example 2.8. Executions of the Beverage Vending Machine, p.25

-/


@[expose] public section

namespace Examples.Executions

open Nemonuri TransitionSystem ExecutionFragmentSpec


def ρ₁ := 𝐸𝑥𝑒𝑐{ts}⸨ &(.pay) ─⌞.insert_coin⌟→ &(.select) ─⌞.τ⌟→ &(.soda) ─⌞.get_soda⌟→ &(.pay)
                    ─⌞.insert_coin⌟→ &(.select) ─⌞.τ⌟→ &(.soda) ─⌞.get_soda⌟→ ... ⸩

def ρ₂ := 𝐸𝑥𝑒𝑐{ts}⸨ &(.select)─⌞.τ⌟→ &(.soda)─⌞.get_soda⌟→ &(.pay)─⌞.insert_coin⌟→ &(.select)─⌞.τ⌟→ &(.beer)─⌞.get_beer⌟→ ...⸩

def ϱ := 𝐸𝑥𝑒𝑐{ts}⸨ &(.pay) ─⌞.insert_coin⌟→ &(.select)─⌞.τ⌟→ &(.soda)─⌞.get_soda⌟→ &(.pay)
                    ─⌞.insert_coin⌟→ &(.select)─⌞.τ⌟→ State.soda ⸩




section Proof1

/-! Execution fragments `ρ₁` and `ϱ` are initial, but `ρ₂` is not. -/

theorem ρ₁_initial (x: ρ₁) : ts.IsInitial x := by
  revert x
  simp [ρ₁]
  intro x lm1
  replace lm1 := EvalToSet.mem_iff_mem.mp lm1
  rcases lm1 with ⟨lm1, lm2⟩
  refine IsInitial.mk lm2 ?_
  simp [exec_spec_norm] at lm1
  cases lm1
  rename_i lm1 lm3
  replace lm1 := lm1.getAt?_eq_at 0
  simp [exec_spec_norm] at lm1
  rewrite [SequenceProd.getAt?_eq_ofProd?_getAt?_at, OptionProd.ext_iff] at lm1
  simp at lm1
  rcases lm1 with ⟨lm1_1, lm1_2⟩
  simp
  rw [← Option.some_inj, ← Sequence.head?_eq_some_head, Sequence.head?_eq_getAt?_zero]
  exact lm1_1.symm


theorem ϱ_initial (x: ϱ) : ts.IsInitial x := by
  revert x
  simp [ϱ]
  intro x lm1
  replace lm1 := EvalToSet.mem_iff_mem.mp lm1
  rcases lm1 with ⟨lm1, lm2⟩
  dsimp at lm1
  refine IsInitial.mk lm2 ?_
  simp
  rw [← Option.some_inj, ← Sequence.head?_eq_some_head, Sequence.head?_eq_getAt?_zero]
  simp [exec_spec_norm] at lm1
  cases lm1
  --simp [lm1.isInitial_iff]
  --have lm2 := lm1.preOrWhole_is_prefix.states_getElem_eq' 0
  --simp at lm2; exact lm2.symm

theorem not_ρ₂_initial (x: ρ₂) : ¬(x: ts.ExecutionFragmentRaw).IsInitial := by
  revert x; simp only [Subtype.forall]; intro x lm1
  simp [ρ₂] at lm1
  refine lm1.isInitial_iff.not.mpr ?_
  have lm2 := lm1.preOrWhole_is_prefix.states_getElem_eq' 0
  simp at lm2
  intro cont; simp at cont
  have lm3 := Eq.trans lm2 cont
  simp at lm3

end Proof1


section Proof2

/-! `ϱ` is not maximal as it does not end in a terminal state.  -/

attribute [local simp] EvalToSet.mem_iff_mem


theorem ϱ_not_maximal (x: ϱ) : ¬(x: ts.ExecutionFragmentRaw).IsMaximal := by
  revert x; simp [ϱ]; intro x lm1
  rintro ⟨lm2, lm3⟩
  rcases lm3 with ⟨⟨xs, lm3⟩, lm4⟩ | _
  · dsimp [IsTerminal, SetOfDirectSuccessor, SetOfDirectSuccessorAt, FiniteExecutionFragment.states] at lm4
    simp at lm1 lm2
    revert lm4
    simp
    suffices goal: (xs.states.getLast ?h1) = State.soda by
      simp [goal]
      exists Act.get_soda
      simp [Set.eq_empty_iff_forall_notMem]
      exists State.pay
      exact Tr.soda_pay
    case h1 => exact (FiniteExecutionFragment.mk xs lm3).states_length_pos |> List.ne_nil_of_length_pos
    rw [List.getLast_eq_iff_getLast?_eq_some]
    refine Eq.trans ((UniqueMem.of_mem_left_whole lm1 ?_).states_eq.symm |> congrArg (List.getLast?)) ?_
    · simp only [toLabel_eq_toLabelAt, stepL_eq_stepLFlip]
      simp [stepLFlip_preserves_label, HasLabel.Preserves.cancel]
    · simp only [stepL_eq_stepLFlip]
      simp [stepLFlip_preserves_label, HasLabel.Preserves.cancel]
  · revert lm1
    refine Mem.not_infinite_finite ?_ ?_
    · dsimp
    · simp only [toSeqLabel_eq_toLabelAt, stepL_eq_stepLFlip]
      simp [stepLFlip_preserves_seqLabel, HasLabel.Preserves.cancel]


/-!  Assuming that `ρ₁` and `ρ₂` are infinite, they are maximal. -/

theorem ρ₁_maximal (x: ρ₁) : (x: ts.ExecutionFragmentRaw).IsMaximal := by
  revert x; simp [ρ₁]; intro x lm1
  refine lm1.isMaximal_of_left_infinite ?_
  simp only [toSeqLabel_eq_toLabelAt, stepL_eq_stepLFlip]
  simp [stepLFlip_preserves_seqLabel, HasLabel.Preserves.cancel]


theorem ρ₂_maximal (x: ρ₂) : (x: ts.ExecutionFragmentRaw).IsMaximal := by
  revert x; simp [ρ₂]; intro x lm1
  refine lm1.isMaximal_of_left_infinite ?_
  simp only [toSeqLabel_eq_toLabelAt, stepL_eq_stepLFlip]
  simp [stepLFlip_preserves_seqLabel, HasLabel.Preserves.cancel]

--#print ρ₂_maximal

end Proof2



end Examples.Executions

end
