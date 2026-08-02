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

namespace ExecutionFragment


inductive IsExpr {ts: TransitionSystem} : ExprRaw ts → Prop where
  | finite1 (total: ts.FiniteExecutionFragmentRaw) (req: ts.IsFiniteExecutionFragment total)
            : IsExpr (.finite1 total)
  | finite2 (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
            (req1: pre.IsPrefixFragment) (req2: post.IsSuffixFragment)
            : IsExpr (.finite2 pre post)
  | infinite1 (pre: ts.FiniteExecutionFragmentRaw) (req: pre.IsPrefixFragment)
            : IsExpr (.infinite1 pre)


structure Expr (ts: TransitionSystem) where
  raw: ExprRaw ts
  is_valid: IsExpr raw


namespace ExprRaw

variable {ts: TransitionSystem}

open FiniteExecutionFragmentRaw

/-
inductive Mem : ts.ExecutionFragment → Expr ts → Prop where
  | finite1 (ef: ts.FiniteExecutionFragment)
            : Mem (.ofFinite ef) ⟨.finite1 ef.raw, .finite1 ef.raw ef.is_valid⟩
  | finite2 (ef: ts.FiniteExecutionFragment) (pre: PrefixFragment ts) (post: SuffixFragment ts)
            (req1: ExecutionFragmentRaw.IsPrefix pre.raw (.finite ef.raw))
            (req2: ExecutionFragmentRaw.IsSuffix post.raw (.finite ef.raw))
            : Mem (.ofFinite ef) ⟨.finite2 pre.raw post.raw, .finite2 pre.raw post.raw pre.is_valid post.is_valid⟩
  | infinite1 (ef: ts.InfiniteExecutionFragment) (pre: PrefixFragment ts)
              (req: ExecutionFragmentRaw.IsPrefix pre.raw (.infinite ef.raw))
              : Mem (.ofInfinite ef) ⟨.infinite1 pre.raw, .infinite1 pre.raw pre.is_valid⟩
-/

inductive Mem : ts.ExecutionFragmentRaw → ExprRaw ts → Prop where
  | finite1 (ef: ts.FiniteExecutionFragment)
            : Mem (.finite ef.raw) (.finite1 ef.raw)
  | finite2 (ef: ts.FiniteExecutionFragment) (pre: PrefixFragment ts) (post: SuffixFragment ts)
            (req1: ExecutionFragmentRaw.IsPrefix pre.raw (.finite ef.raw))
            (req2: ExecutionFragmentRaw.IsSuffix post.raw (.finite ef.raw))
            : Mem (.finite ef.raw) (.finite2 pre.raw post.raw)
  | infinite1 (ef: ts.InfiniteExecutionFragment) (pre: PrefixFragment ts)
              (req: ExecutionFragmentRaw.IsPrefix pre.raw (.infinite ef.raw))
              : Mem (.infinite ef.raw) (.infinite1 pre.raw)

theorem mem_imp_isExecutionFragment ef ex (h: @Mem ts ef ex) : ts.IsExecutionFragment ef := by
  cases h with
  | finite1 ef =>
    refine .finite _ ?_
    exact ef.is_valid
  | finite2 ef _ _ _ _ =>
    refine .finite _ ?_
    exact ef.is_valid
  | infinite1 ef pre req =>
    refine .infinite _ ?_
    exact ef.is_valid

theorem mem_imp_isExpr ef ex (h: @Mem ts ef ex) : IsExpr ex := by
  cases h with
  | finite1 ef =>
    exact .finite1 ef.raw ef.is_valid
  | finite2 ef pre post _ _ =>
    exact .finite2 pre.raw post.raw pre.is_valid post.is_valid
  | infinite1 ef pre _ =>
    exact .infinite1 pre.raw pre.is_valid


theorem mem_finite1_imp_eq {fef1 fef2} (h: @Mem ts (.finite fef1) (.finite1 fef2))
  : (fef1 = fef2) := by
  cases h; rfl


def EvalToSet (ex: ExprRaw ts) : Set ts.ExecutionFragmentRaw := {ef | Mem ef ex}



end ExprRaw



end ExecutionFragment

end Nemonuri.TransitionSystem

end
