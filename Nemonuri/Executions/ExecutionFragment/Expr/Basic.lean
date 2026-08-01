module

public import Nemonuri.Executions.ExecutionFragment.Expr.Raw
public import Nemonuri.Executions.ExecutionFragment.Basic
--public import Nemonuri.Executions.ExecutionFragment.PrefixPostfix

@[expose] public section

namespace Nemonuri.TransitionSystem

namespace FiniteExecutionFragmentRaw

variable {ts: TransitionSystem}

inductive IsPrefixFragment : ts.FiniteExecutionFragmentRaw → Prop where
  | intro (states: List ts.S) (actions: List ts.Act) (stateLast: ts.S)
          (req: ts.IsFiniteExecutionFragment ⟨states ++ [stateLast], actions⟩)
          : IsPrefixFragment ⟨states ++ [stateLast], actions⟩

inductive IsPostfixFragment : ts.FiniteExecutionFragmentRaw → Prop where
  | intro (states: List ts.S) (actions: List ts.Act) (state0: ts.S)
          (req: ts.IsFiniteExecutionFragment ⟨state0 :: states, actions⟩)
          : IsPostfixFragment ⟨state0 :: states, actions⟩

end FiniteExecutionFragmentRaw

namespace ExecutionFragment


inductive IsExpr {ts: TransitionSystem} : ExprRaw ts → Prop where
  | finite1 (total: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment total)
            : IsExpr (.finite1 total)
  | finite2 (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
            (req1: pre.IsPrefixFragment) (req2: post.IsPostfixFragment)
            : IsExpr (.finite2 pre post)
  | infinite1 (pre: ts.FiniteExecutionFragmentRaw) (req: pre.IsPrefixFragment)
            : IsExpr (.infinite1 pre)


structure Expr (ts: TransitionSystem) where
  raw: ExprRaw ts
  is_valid: IsExpr raw


namespace Expr

variable {ts: TransitionSystem}

/-
inductive Mem : ts.ExecutionFragment → Expr ts → Prop where
  | finite1 (ef: ts.FiniteExecutionFragment)
            : Mem (.ofFinite ef) ⟨.finite1 ef.raw, .finite1 ef.raw ef.is_valid⟩
  |
-/


end Expr



end ExecutionFragment

end Nemonuri.TransitionSystem

end
