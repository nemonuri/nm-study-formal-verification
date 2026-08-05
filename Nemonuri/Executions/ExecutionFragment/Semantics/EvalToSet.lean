module

public import Nemonuri.Executions.ExecutionFragment.Semantics.Mem

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

variable {ts: TransitionSystem}



def EvalToSet (coll: SyntaxRaw ts) : Set ts.ExecutionFragmentRaw := {elem | Mem coll elem}

namespace EvalToSet

variable {coll: SyntaxRaw ts} {elem: ExecutionFragmentRaw ts}

theorem mem_to_isExecutionFragment (h: elem ∈ coll.EvalToSet)
  : ts.IsExecutionFragment elem :=
  SyntaxRaw.Mem.is_executionFragment h

theorem mem_iff_mem : (elem ∈ coll.EvalToSet) ↔ Mem coll elem := by
  dsimp [EvalToSet]; rfl


end EvalToSet

end Nemonuri.TransitionSystem.ExecutionFragment.SyntaxRaw

end
