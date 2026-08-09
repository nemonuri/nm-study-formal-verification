module

public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Tactic.DeriveFintype
public import Nemonuri.Sequence.Labels


@[expose] public section

namespace Nemonuri



structure Sequence (α: Type _) where
  getAt? : ℕ → (Option α)
  length? : ℕ∞
  length?_getAt? {i: ℕ} : (i < length?) ↔ (getAt? i).isSome

namespace Sequence

variable {α: Type _} {seq: Sequence α}

instance : GetElem? (Sequence α) ℕ α (fun seq i => i < seq.length?) where
  getElem seq i h := (seq.getAt? i).get (seq.length?_getAt?.mp h)
  getElem? seq i := (seq.getAt? i)

instance : LawfulGetElem (Sequence α) ℕ α (fun seq i => i < seq.length?) where
  getElem?_def seq i := by
    simp [length?_getAt?]
    split <;> rename_i lm1
    · rw [Option.eq_some_iff_get_eq]
      refine Exists.intro ?_ ?_
      · exact lm1
      · rfl
    · simp at lm1
      exact lm1

def toEmptyLabel (seq: Sequence α) : EmptyLabel := .ofENat seq.length?

def toFinLabel (seq: Sequence α) : FiniteLabel := .ofENat seq.length?

open scoped EmptyLabel FiniteLabel in
theorem not_empty_infinite (req1: seq.toEmptyLabel = .empty) (req2: seq.toFinLabel = .infinite) : False := by
  dsimp [toEmptyLabel] at req1
  dsimp [toFinLabel] at req2
  cases lm1: seq.length?
  · simp [lm1] at req1
  · simp [lm1] at req2


def head (seq: Sequence α) (req: seq.toEmptyLabel = .nonempty) : α :=
  seq[0]'(by
    dsimp [toEmptyLabel] at req
    rw [EmptyLabel.ofENat_nonempty_iff_pos] at req
    simpa using req)

def head? (seq: Sequence α) : Option α :=
  match lm1: seq.toEmptyLabel with
  | .nonempty => .some (seq.head lm1)
  | .empty => .none

theorem head?_eq_some_head (req: seq.toEmptyLabel = .nonempty) : seq.head? = .some (seq.head req) := by
  dsimp [head?]
  split <;> rename_i heq
  · rfl
  · simp [heq] at req

open scoped FiniteLabel in
def length (seq: Sequence α) (req: seq.toFinLabel = .finite) : ℕ :=
  seq.length?.lift (by
    dsimp [toFinLabel] at req
    rw [FiniteLabel.ofENat_finite_iff_lt_top] at req
    exact req )

theorem length?_eq_natCast_length (req: seq.toFinLabel = .finite) : seq.length? = Nat.cast (seq.length req) := by
  dsimp [length]
  revert req
  simp [toFinLabel, FiniteLabel.ofENat_finite_iff_lt_top]

def last (seq: Sequence α) (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite) :=
  seq[(seq.length req2) - 1]'(by
    rw [seq.length?_eq_natCast_length req2]
    simp only [ENat.coe_lt_coe]
    refine Nat.sub_one_lt ?_
    simp [toEmptyLabel, EmptyLabel.ofENat_nonempty_iff_pos] at req1
    intro lm1
    replace lm1 := congrArg (@Nat.cast ENat _) lm1
    rw [← length?_eq_natCast_length] at lm1
    rw [lm1] at req1
    simp at req1 )



end Sequence

--[FunLike F α (Option β)]
class SequenceLike (F: Type _) (α: Type _) where
  toGetAt? : F → ℕ → (Option α)
  toLength? : F → ℕ∞
  toLength?_toGetAt? {f: F} {i: ℕ} : (i < (toLength? f)) ↔ (toGetAt? f i).isSome
  inj {f1 f2: F} : (toGetAt? f1) = (toGetAt? f2) → (toLength? f1) = (toLength? f2) → f1 = f2
  --length?_valid (i: ℕ) (req: i <) :




end Nemonuri

end
