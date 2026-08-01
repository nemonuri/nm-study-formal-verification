module

public import Nemonuri.Executions.ExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment

inductive ExprRaw (ts: TransitionSystem) where
  | finite1 (total: ts.FiniteExecutionFragmentRaw)
  | finite2 (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
  | infinite1 (pre: ts.FiniteExecutionFragmentRaw)



end Nemonuri.TransitionSystem.ExecutionFragment

end
