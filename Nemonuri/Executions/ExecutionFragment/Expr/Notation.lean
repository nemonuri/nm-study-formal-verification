module

public import Nemonuri.Executions.ExecutionFragment.Expr.Basic

@[expose] public meta section

namespace Nemonuri.TransitionSystem.ExecutionFragment.Expr

open ExprRaw

open Lean

declare_syntax_cat exec_expr

--syntax execExprOrTerm := exec_expr:1 <|> term:0

syntax:max " 𝐸𝑥𝑒𝑐{" term "}⸨ " exec_expr " ⸩" : term
--syntax:(max-1) " 𝐸𝑥𝑒𝑐{" term "}⸨ " term " ⸩" : term
--syntax:max "𝐸𝑥𝑒𝑐% " term : exec_expr


macro_rules
  | `( 𝐸𝑥𝑒𝑐{ $ts:term }⸨ $expr:exec_expr ⸩ ) => do ``( @ExprRaw.EvalToSet $ts $(.mk (← pure expr)) )

--  | `( 𝐸𝑥𝑒𝑐{ $ts:term }⸨ $expr:term ⸩ ) => `( 𝐸𝑥𝑒𝑐{ $ts }⸨ 𝐸𝑥𝑒𝑐% $expr ⸩ )
--  | `(exec_expr| 𝐸𝑥𝑒𝑐% $t) => ``(ExprRaw.singleState $t)
-- let expr0 : TSyntax `term := .mk expr.raw;

syntax:max ident : exec_expr
syntax:max "&(" term:min ")" : exec_expr

macro_rules
  | `(exec_expr| &( $tm:term )) => `($tm)
  | `(exec_expr| $i:ident) => `($i)


syntax:100 exec_expr:99 "─⌞" term "⌟→" exec_expr:100 : exec_expr

macro_rules
  | `(exec_expr| $s:exec_expr ─⌞ $a:term ⌟→ $tail:exec_expr ) => do `(ExprRaw.stepL $(.mk (← pure tail)) $(.mk (← pure s)) $a)



syntax:102 "..." : exec_expr
syntax:104 "..." exec_expr:104 : exec_expr


macro_rules
  | `(exec_expr| ...) => `(ExprRaw.ellipsis)
  | `(exec_expr| ... $expr:exec_expr ) => do `(ExprRaw.consEllipsis $(.mk (← pure expr)))


end Nemonuri.TransitionSystem.ExecutionFragment.Expr

end
