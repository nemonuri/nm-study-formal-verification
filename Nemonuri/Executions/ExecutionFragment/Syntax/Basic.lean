module

public import Nemonuri.Executions.ExecutionFragment.Syntax.Raws
--public import Nemonuri.Executions.ExecutionFragment.Basic
--public import Nemonuri.Executions.ExecutionFragment.Maximal
public import Nemonuri.Executions.FiniteExecutionFragment.Prefix

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment

--namespace SyntaxRaw

inductive IsSyntax {ts: TransitionSystem} : SyntaxRaw ts → Prop where
  | unique (whole: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment whole)
            : IsSyntax (.unique whole)
  | finites (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
            (req1: pre.IsPrefixFragment) (req2: post.IsSuffixFragment)
            : IsSyntax (.finites pre post)
  | infinites (pre: ts.FiniteExecutionFragmentRaw) (req: pre.IsPrefixFragment)
            : IsSyntax (.infinites pre)

--end SyntaxRaw


structure Syntax (ts: TransitionSystem) where
  raw: SyntaxRaw ts
  is_valid: IsSyntax raw


end Nemonuri.TransitionSystem.ExecutionFragment

end
