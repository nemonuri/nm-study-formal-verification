module

public import Nemonuri.Executions.ExecutionFragment.Expr.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

variable {ts: TransitionSystem}


open FiniteExecutionFragmentRaw


inductive Mem : ExprRaw ts → ts.ExecutionFragmentRaw → Prop where
  | finite1 (ef: ts.FiniteExecutionFragment)
            : Mem (.finite1 ef.raw) (.finite ef.raw)
  | finite2 (ef: ts.FiniteExecutionFragment) (pre: PrefixFragment ts) (post: SuffixFragment ts)
            (req1: ExecutionFragmentRaw.IsPrefix pre.raw (.finite ef.raw))
            (req2: ExecutionFragmentRaw.IsSuffix post.raw (.finite ef.raw))
            : Mem (.finite2 pre.raw post.raw) (.finite ef.raw)
  | infinite1 (ef: ts.InfiniteExecutionFragment) (pre: PrefixFragment ts)
              (req: ExecutionFragmentRaw.IsPrefix pre.raw (.infinite ef.raw))
              : Mem (.infinite1 pre.raw) (.infinite ef.raw)

namespace Mem

variable {coll: ExprRaw ts} {elem: ts.ExecutionFragmentRaw}

theorem is_executionFragment (h: Mem coll elem) : ts.IsExecutionFragment elem := by
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


theorem label_eq (h: Mem coll elem)
  : elem.toLabel = coll.toSeqLabel := by
  cases h <;> dsimp

theorem not_finite_infinite
  (h1: elem.toLabel = .finite) (h2: coll.toSeqLabel = .infinite)
  : ¬(Mem coll elem) := by
  intro cont
  have lm1 := cont.label_eq
  simp [h1, h2] at lm1

theorem not_infinite_finite
  (h1: elem.toLabel = .infinite) (h2: coll.toSeqLabel = .finite)
  : ¬(Mem coll elem) := by
  intro cont
  have lm1 := cont.label_eq
  simp [h1, h2] at lm1


theorem is_expr (h: @Mem ts coll elem) : IsExpr coll := by
  cases h with
  | finite1 ef =>
    exact .finite1 ef.raw ef.is_valid
  | finite2 ef pre post _ _ =>
    exact .finite2 pre.raw post.raw pre.is_valid post.is_valid
  | infinite1 ef pre _ =>
    exact .infinite1 pre.raw pre.is_valid



theorem pre_is_prefix (h: Mem coll elem) : ExecutionFragmentRaw.IsPrefix coll.pre elem := by
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
theorem pre_getElem_eq (h: Mem ef ex) (i: Nat) (req: i < coll.pre.states.length)
  : ex.pre.states[i]'(req) = ef.states[i]'()
-/

theorem post_is_suffix (h: Mem coll elem) (req: elem.toLabel = .finite) : ExecutionFragmentRaw.IsSuffix (coll.post (h.label_eq ▸ req)) elem := by
  cases h
  · dsimp; constructor <;> exact Sequence.IsSuffix.refl _
  · dsimp; assumption
  · simp at req




/-
theorem finite1_imp_eq {fef1 fef2} (h: @Mem ts (.finite fef1) (.finite1 fef2))
  : (fef1 = fef2) := by
  cases h; rfl

theorem unique_of_toLabel_finite1 (h: Mem ef ex) (req: ex.toLabel = .finite1) (ef': ts.ExecutionFragmentRaw) (h': Mem ef' ex)
  : ef' = ef := by
  cases h <;> simp at req
  have lm1 := h'.label_eq
  dsimp at lm1
  cases ef' <;> simp at lm1
  rw [h'.finite1_imp_eq]
-/


def toExecutionFragment (req: Mem coll elem) : ts.ExecutionFragment := ⟨elem, req.is_executionFragment⟩

def toExpr (req: Mem coll elem) : Expr ts := ⟨coll, req.is_expr⟩


theorem states_length?_pos (h: Mem coll elem) : 0 < elem.states.length? := h.toExecutionFragment.states_length?_pos


theorem isInitial_iff (h: Mem coll elem)
  : elem.IsInitial ↔ (elem.states[0]'(h.states_length?_pos) ∈ ts.I) := by
  constructor
  · rintro ⟨lm1, lm2⟩
    dsimp [ExecutionFragment.IsInitial] at lm2
    exact lm2
  · intro lm1
    dsimp [ExecutionFragmentRaw.IsInitial]
    exists h.is_executionFragment

/-
theorem isMaximal_iff (h: Mem ef ex)
  : ef.IsMaximal ↔ (ef.states[ef.states.len])
-/

end Mem



end Nemonuri.TransitionSystem.ExecutionFragment.ExprRaw

end
