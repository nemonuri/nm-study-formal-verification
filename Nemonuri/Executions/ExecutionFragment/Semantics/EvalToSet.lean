module

public import Nemonuri.Executions.ExecutionFragment.Semantics.Mem

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

variable {ts: TransitionSystem}



def EvalToSet (coll: ExprRaw ts) : Set ts.ExecutionFragmentRaw := {elem | Mem coll elem}

namespace EvalToSet

variable {coll: ExprRaw ts} {elem: ExecutionFragmentRaw ts}

theorem mem_to_isExecutionFragment (h: elem ∈ coll.EvalToSet)
  : ts.IsExecutionFragment elem :=
  ExprRaw.Mem.is_executionFragment h

theorem mem_iff_mem : (elem ∈ coll.EvalToSet) ↔ Mem coll elem := by
  dsimp [EvalToSet]; rfl

end EvalToSet

end Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

end
