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
  rename_i lm1
  replace lm1 := lm1.getAt?_eq_at 0
  simp [exec_spec_norm] at lm1
  simp [OptionProd.ext_iff, SequenceProd.getAt?_fst?_eq_fst_getAt?_at, SequenceProd.getAt?_snd?_eq_snd_getAt?_at] at lm1
  rcases lm1 with ⟨lm1_1, lm1_2⟩
  simp
  rw [Sequence.head_eq_iff_getAt?_zero_eq_some]
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
  rw [Sequence.head_eq_iff_getAt?_zero_eq_some, ← SequenceProd.getAt?_fst?_eq_fst_getAt?_at]
  simp [exec_spec_norm] at lm1
  cases lm1
  simp [exec_spec_norm]


theorem not_ρ₂_initial (x: ρ₂) : ¬(ts.IsInitial x) := by
  revert x; simp only [Subtype.forall]; intro x lm1
  simp [ρ₂] at lm1
  rw [EvalToSet.mem_iff_mem] at lm1
  simp [exec_spec_norm] at lm1
  rcases lm1 with ⟨lm1, lm2⟩; clear lm2
  dsimp only at lm1
  intro lm3
  rcases lm3 with ⟨lm2, lm3⟩
  simp at lm3
  rewrite [Sequence.head_eq_iff_getAt?_zero_eq_some] at lm3
  cases lm1
  rename_i lm1
  replace lm1 := lm1.getAt?_eq_at 0
  simp [exec_spec_norm] at lm1
  simp [OptionProd.ext_iff, SequenceProd.getAt?_fst?_eq_fst_getAt?_at] at lm1
  rcases lm1 with ⟨lm1, lm5⟩
  simp [← lm1] at lm3


end Proof1


section Proof2


/-! `ϱ` is not maximal as it does not end in a terminal state.  -/

theorem ϱ_not_maximal (x: ϱ) : ¬(ts.IsMaximal x) := by
  revert x; simp [ϱ]; intro x lm1
  rintro ⟨lm2, lm3⟩
  replace lm1 := EvalToSet.mem_iff_mem.mp lm1
  simp [exec_spec_norm] at lm1
  replace lm1 := lm1.subSpec_mem
  dsimp at lm1
  simp at lm3
  conv at lm3 =>
    arg 2
    arg 2
    dsimp [IsTerminal, SetOfDirectSuccessor, SetOfDirectSuccessorAt]
    simp
  cases lm1
  conv at lm3 =>
    arg 2
    arg 1
    rw [Sequence.last?_eq_getFromLastAt?_zero, Sequence.getFromLastAt?_eq_some_iff_getAt?_eq_some]
    simp [← SequenceProd.getAt?_fst?_eq_fst_getAt?_at, exec_spec_norm]
  simp [Set.ext_iff] at lm3
  refine lm3 5 ?_ Act.get_soda State.pay ?_
  · simp only [← ENat.coe_one, ← ENat.coe_add]
  · exact Tr.soda_pay


/-!  Assuming that `ρ₁` and `ρ₂` are infinite, they are maximal. -/

theorem ρ₁_maximal (h: ρ₁ ⊆ SequenceProd.InfiniteSet) (x: ρ₁) : ts.IsMaximal x := by
  revert x h; simp [Set.subset_def]
  intro lm1 x lm2
  specialize lm1 x lm2
  dsimp [SequenceProd.InfiniteSet] at lm1
  rcases lm1 with ⟨lm1, lm3⟩
  simp [ρ₁, exec_spec_norm] at lm2
  replace lm2 := EvalToSet.mem_iff_mem.mp lm2
  replace lm2 := lm2.executionFragment
  exact lm2.maximal_of_infinite lm3

theorem ρ₂_maximal (h: ρ₂ ⊆ SequenceProd.InfiniteSet) (x: ρ₂) : ts.IsMaximal x := by
  revert x h; simp [Set.subset_def]
  intro lm1 x lm2
  specialize lm1 x lm2
  dsimp [SequenceProd.InfiniteSet] at lm1
  rcases lm1 with ⟨lm1, lm3⟩
  simp [ρ₂, exec_spec_norm] at lm2
  replace lm2 := EvalToSet.mem_iff_mem.mp lm2 |>.executionFragment
  exact lm2.maximal_of_infinite lm3

end Proof2



end Examples.Executions

end
