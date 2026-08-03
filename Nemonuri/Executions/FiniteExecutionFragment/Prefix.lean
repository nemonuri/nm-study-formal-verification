module

public import Nemonuri.Executions.FiniteExecutionFragment.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem

namespace FiniteExecutionFragmentRaw

variable {ts: TransitionSystem}

inductive IsPrefixFragment : ts.FiniteExecutionFragmentRaw → Prop where
  | intro (states: List ts.S) (actions: List ts.Act) (stateLast: ts.S)
          (req: ts.IsFiniteExecutionFragment ⟨states ++ [stateLast], actions⟩)
          : IsPrefixFragment ⟨states ++ [stateLast], actions⟩

inductive IsSuffixFragment : ts.FiniteExecutionFragmentRaw → Prop where
  | intro (states: List ts.S) (actions: List ts.Act) (state0: ts.S)
          (req: ts.IsFiniteExecutionFragment ⟨state0 :: states, actions⟩)
          : IsSuffixFragment ⟨state0 :: states, actions⟩


structure PrefixFragment (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: IsPrefixFragment raw

structure SuffixFragment (ts: TransitionSystem) where
  raw: ts.FiniteExecutionFragmentRaw
  is_valid: IsSuffixFragment raw

end FiniteExecutionFragmentRaw

end Nemonuri.TransitionSystem

end
