module

public import Nemonuri.Executions.ExecutionFragment.Expr.Raw
public import Nemonuri.Executions.ExecutionFragment.Basic
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

namespace Mem

variable {ef: ts.ExecutionFragmentRaw} {ex: ExprRaw ts}

theorem is_executionFragment (h: Mem ef ex) : ts.IsExecutionFragment ef := by
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


theorem label_eq (h: Mem ef ex)
  : ef.toLabel = ex.toSeqLabel := by
  cases h <;> dsimp

theorem not_finite_infinite
  (h1: ef.toLabel = .finite) (h2: ex.toSeqLabel = .infinite)
  : ¬(Mem ef ex) := by
  intro cont
  have lm1 := cont.label_eq
  simp [h1, h2] at lm1

theorem not_infinite_finite
  (h1: ef.toLabel = .infinite) (h2: ex.toSeqLabel = .finite)
  : ¬(Mem ef ex) := by
  intro cont
  have lm1 := cont.label_eq
  simp [h1, h2] at lm1


theorem is_expr (h: @Mem ts ef ex) : IsExpr ex := by
  cases h with
  | finite1 ef =>
    exact .finite1 ef.raw ef.is_valid
  | finite2 ef pre post _ _ =>
    exact .finite2 pre.raw post.raw pre.is_valid post.is_valid
  | infinite1 ef pre _ =>
    exact .infinite1 pre.raw pre.is_valid


theorem pre_is_prefix (h: Mem ef ex) : ExecutionFragmentRaw.IsPrefix ex.pre ef := by
  cases h <;> dsimp
  · constructor <;> exact Sequence.IsPrefix.refl _
  · assumption
  · assumption

/-
theorem pre_lt_states_length_imp_lt_states_length? (h: Mem ef ex) (i: Nat) (req: i < ex.pre.states.length)
  : (i < ef.states.length?) := by
  cases ef
  · simp
    · cases ex <;> dsimp at req
-/
  --cases ex
  --· dsimp at req
  --cases ex
  --· dsimp

/-
theorem pre_getElem_eq (h: Mem ef ex) (i: Nat) (req: i < ex.pre.states.length)
  : ex.pre.states[i]'(req) = ef.states[i]'()
-/

theorem post_is_suffix (h: Mem ef ex) (req: ef.toLabel = .finite) : ExecutionFragmentRaw.IsSuffix (ex.post (h.label_eq ▸ req)) ef := by
  cases h
  · dsimp; constructor <;> exact Sequence.IsSuffix.refl _
  · dsimp; assumption
  · simp at req


theorem finite1_imp_eq {fef1 fef2} (h: @Mem ts (.finite fef1) (.finite1 fef2))
  : (fef1 = fef2) := by
  cases h; rfl


def toExecutionFragment (req: Mem ef ex) : ts.ExecutionFragment := ⟨ef, req.is_executionFragment⟩

def toExpr (req: Mem ef ex) : Expr ts := ⟨ex, req.is_expr⟩


--theorem


end Mem





def EvalToSet (ex: ExprRaw ts) : Set ts.ExecutionFragmentRaw := {ef | Mem ef ex}

theorem EvalToSet.mem_imp_isExecutionFragment
  (ef: ExecutionFragmentRaw ts) (ex: ExprRaw ts) (h: ef ∈ ex.EvalToSet)
  : ts.IsExecutionFragment ef :=
  ExprRaw.Mem.is_executionFragment h



end ExprRaw



end ExecutionFragment

end Nemonuri.TransitionSystem

end
