module

public import Nemonuri.Executions.ExecutionFragment.Semantics.Mem

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

variable {ts: TransitionSystem}

def UniqueMem (coll elem: ts.FiniteExecutionFragmentRaw) : Prop := Mem (.unique coll) (.finite elem)

@[defeq]
theorem uniqueMem_def {coll elem} : (@UniqueMem ts coll elem) = Mem (.unique coll) (.finite elem) := rfl


namespace UniqueMem

variable {coll elem elem2: ts.FiniteExecutionFragmentRaw}


theorem mk (req: Mem (.unique coll) (.finite elem)) : UniqueMem coll elem := req

theorem of_mem
  {coll2 elem2} (req1: Mem coll2 elem2) (req2: coll2 = (.unique coll)) (req3: elem2 = (.finite elem)) : UniqueMem coll elem :=
  req1.congr_iff req2 req3 |> UniqueMem.mk

theorem of_mem_left {coll2} (req1: Mem coll2 (.finite elem)) (req2: coll2 = (.unique coll)) : UniqueMem coll elem :=
  UniqueMem.of_mem req1 req2 rfl

theorem to_mem (h: UniqueMem coll elem) : Mem (.unique coll) (.finite elem) := uniqueMem_def.mp h



theorem to_eq (h: UniqueMem coll elem) : coll = elem := by
  dsimp [uniqueMem_def] at h; cases h; rfl

theorem states_eq (h: UniqueMem coll elem) : coll.states = elem.states := h.to_eq |> congrArg _

theorem actions_eq (h: UniqueMem coll elem) : coll.actions = elem.actions := h.to_eq |> congrArg _



theorem symm (h: UniqueMem coll elem) : UniqueMem elem coll := by
  have lm1 := h.to_eq
  revert h
  simp [lm1]

instance : Std.Symm (@UniqueMem ts) := ⟨@UniqueMem.symm ts⟩

theorem symm_iff : (UniqueMem coll elem) ↔ (UniqueMem elem coll) := ⟨UniqueMem.symm, UniqueMem.symm⟩


theorem trans (hl: UniqueMem coll elem) (hr: UniqueMem elem elem2) : UniqueMem coll elem2 := by
  simpa [hr.to_eq] using hl

instance : IsTrans ts.FiniteExecutionFragmentRaw (@UniqueMem ts) := ⟨fun a b c => @UniqueMem.trans _ a b c⟩


theorem refl (x: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment x) : UniqueMem x x := by
  dsimp [uniqueMem_def]
  exact Mem.unique (.mk x req)

theorem refl_iff : UniqueMem elem elem ↔ ts.IsFiniteExecutionFragment elem := by
  constructor
  · intro lm1
    dsimp [uniqueMem_def] at lm1
    replace lm1 := lm1.is_executionFragment
    cases lm1; assumption
  · exact UniqueMem.refl _


theorem of_mem_left_whole
  {coll} (req1: Mem coll (.finite elem)) (req2: coll.toLabel = .unique) --(req3: coll.whole req2 = elem)
  : UniqueMem (coll.whole req2) elem := by
  refine UniqueMem.of_mem_left req1 ?_
  cases coll
  · dsimp
  · simp at req2
  · simp at req2
/-
  cases coll
  · dsimp
    have lm1 := (UniqueMem.mk req1).to_eq |>.symm
    subst lm1
    rw [refl_iff]
    have lm2 := req1.is_executionFragment
    cases lm2
    assumption
  · simp at req2
  · simp at req2
-/




/-
theorem iff_eq (req: ts.IsFiniteExecutionFragment coll ∨ ts.IsFiniteExecutionFragment elem)
  : UniqueMem coll elem ↔ coll = elem := by
  constructor
  · exact to_eq
  · intro lm1; subst lm1
    refine UniqueMem.refl coll ?_
    simpa using req
-/





end UniqueMem


end Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

end
