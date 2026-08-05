module

public import Nemonuri.Executions.ExecutionFragment.Semantics.Mem

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

variable {ts: TransitionSystem}

def UniqueMem (coll elem: ts.FiniteExecutionFragmentRaw) : Prop := ExprRaw.Mem (.finite1 coll) (.finite elem)

@[defeq]
theorem uniqueMem_def {coll elem} : (@UniqueMem ts coll elem) = ExprRaw.Mem (.finite1 coll) (.finite elem) := rfl


namespace UniqueMem

variable {coll elem elem2: ts.FiniteExecutionFragmentRaw}

--attribute [local simp low] uniqueMem_def

theorem to_mem (h: UniqueMem coll elem) : ExprRaw.Mem (.finite1 coll) (.finite elem) := uniqueMem_def.mp h

--theorem refl (fef: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment fef) : UniqueMem fef fef := Mem.finite1 (.mk fef req)

theorem to_eq (h: UniqueMem coll elem) : coll = elem := by
  dsimp [uniqueMem_def] at h; cases h; rfl

theorem symm (h: UniqueMem coll elem) : UniqueMem elem coll := by
  have lm1 := h.to_eq
  revert h
  simp [lm1]

instance : Std.Symm (@UniqueMem ts) := ⟨@UniqueMem.symm ts⟩

theorem symm_iff : (UniqueMem coll elem) ↔ (UniqueMem elem coll) := ⟨UniqueMem.symm, UniqueMem.symm⟩


theorem trans (hl: UniqueMem coll elem) (hr: UniqueMem elem elem2) : UniqueMem coll elem2 := by
  simpa [hr.to_eq] using hl

instance : IsTrans ts.FiniteExecutionFragmentRaw (@UniqueMem ts) := ⟨fun a b c => @UniqueMem.trans _ a b c⟩


theorem to_refl (x: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment x) : UniqueMem x x := by
  dsimp [uniqueMem_def]
  exact Mem.finite1 (.mk x req)



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


end Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

end
