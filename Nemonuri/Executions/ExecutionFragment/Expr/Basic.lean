module

public import Nemonuri.Executions.ExecutionFragment.Expr.Raw
public import Nemonuri.Executions.ExecutionFragment.Expr.Pre
public import Nemonuri.Executions.ExecutionFragment.Basic
public import Nemonuri.Executions.ExecutionFragment.Maximal
public import Nemonuri.Executions.FiniteExecutionFragment.Prefix

@[expose] public section

namespace Nemonuri.TransitionSystem

namespace ExecutionFragment


inductive IsExpr {ts: TransitionSystem} : ExprRaw ts → Prop where
  | finite1 (total: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment total)
            : IsExpr (.finite1 total)
  | finite2 (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
            (req1: pre.IsPrefixFragment) (req2: post.IsSuffixFragment)
            : IsExpr (.finite2 pre post)
  | infinite1 (pre: ts.FiniteExecutionFragmentRaw) (req: pre.IsPrefixFragment)
            : IsExpr (.infinite1 pre)

namespace IsExpr

variable {ts: TransitionSystem}

/-
noncomputable def toLabel {ex} : (@IsExpr ts ex) → ExprRaw.Label
  | .finite1 .. => .finite1
  | .finite2 .. => .finite2
  | .infinite1 .. => .infinite1
-/

/-
def toLabel : ExprRaw ts → ExprRaw.Label
  | .finite1 .. => .finite1
  | .finite2 .. => .finite2
  | .infinite1 .. => .infinite1
-/

--def toSeqLabel ()


end IsExpr


structure Expr (ts: TransitionSystem) where
  raw: ExprRaw ts
  is_valid: IsExpr raw



namespace ExprRaw

variable {ts: TransitionSystem}


end ExprRaw



end ExecutionFragment

end Nemonuri.TransitionSystem

end
