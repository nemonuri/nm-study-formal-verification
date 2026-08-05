module

public import Nemonuri.Executions.ExecutionFragment.Syntax.Raws
public import Nemonuri.Executions.ExecutionFragment.Semantics.EvalToSet

@[expose] public meta section

namespace Nemonuri.TransitionSystem.ExecutionFragment

open SyntaxRaw

open Lean

declare_syntax_cat exec_expr


syntax:max " 𝐸𝑥𝑒𝑐{" term "}⸨ " exec_expr " ⸩" : term



macro_rules
  | `( 𝐸𝑥𝑒𝑐{ $ts:term }⸨ $expr:exec_expr ⸩ ) => do ``( @SyntaxRaw.EvalToSet $ts $(.mk (← pure expr)) )


syntax:max ident : exec_expr
syntax:max "&(" term:min ")" : exec_expr

macro_rules
  | `(exec_expr| &( $tm:term )) => `($tm)
  | `(exec_expr| $i:ident) => `($i)


syntax:100 exec_expr:99 "─⌞" term "⌟→" exec_expr:100 : exec_expr


macro_rules
  | `(exec_expr| $s:exec_expr ─⌞ $a:term ⌟→ $tail:exec_expr ) => do `(SyntaxRaw.stepL $(.mk (← pure tail)) $(.mk (← pure s)) $a)



syntax:102 "..." : exec_expr
syntax:104 "..." exec_expr:104 : exec_expr


macro_rules
  | `(exec_expr| ...) => `(SyntaxRaw.ellipsis)
  | `(exec_expr| ... $expr:exec_expr ) => do `(SyntaxRaw.consEllipsis $(.mk (← pure expr)))


end Nemonuri.TransitionSystem.ExecutionFragment

end
