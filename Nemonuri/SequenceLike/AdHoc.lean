module

public import Nemonuri.SequenceLike.Instances

@[expose] public section

namespace Nemonuri.SequenceLike

open Cslib

inductive AdHoc (α: Type) where
  | finite (as: List α)
  | infinite (as: ωSequence α)

variable {α: Type _}

namespace AdHoc

def getAt? (seq: AdHoc α) (i: ℕ) : Option α :=
  match seq with
  | .finite as => Sequence.getAt? as i
  | .infinite as => Sequence.getAt? as i

def length? (seq: AdHoc α) : ℕ∞ :=
  match seq with
  | .finite as => @Sequence.length? α as
  | .infinite as => @Sequence.length? α as



theorem getAt?_injective : Function.Injective (@getAt? α) := by
  intro seq1 seq2 lm1
  rewrite [funext_iff] at lm1
  dsimp [getAt?] at lm1
  split at lm1 <;> rename_i seq1 as1
  · split at lm1 <;> rename_i seq2 as2
    · congr
      refine toSequenceAt_getAt?_ext ?_
      exact funext lm1
    · specialize lm1 as1.length
      simp [← toGetAt?_eq_toSequence_getAt?, seqlike_norm] at lm1
  · split at lm1 <;> rename_i seq2 as2
    · specialize lm1 as2.length
      simp [← toGetAt?_eq_toSequence_getAt?, seqlike_norm] at lm1
    · congr
      refine toSequenceAt_getAt?_ext ?_
      exact funext lm1

end AdHoc




instance ofAdHoc : SequenceLike (AdHoc α) α where
  toSturct := {
    toGetAt? := AdHoc.getAt?
    toLength? := AdHoc.length?
    toLength?_toGetAt? {_ _} := by
      dsimp [AdHoc.getAt?, AdHoc.length?]
      split <;> (
        dsimp [← toLength?_eq_toSequence_length?, ← toGetAt?_eq_toSequence_getAt?]
        exact toLength?_toGetAt? ) }
  inj := AdHoc.getAt?_injective.eq_iff.mp

namespace AdHoc


def consOp : ConsOp (AdHoc α) α where
  consBy a seq :=
    AdHoc.casesOn
      seq
      (fun as => List.consOp.consBy a as |> AdHoc.finite)
      (fun as => ωSequence.consOp.consBy a as |> AdHoc.infinite)
  consBy_head := by
    intro a seq
    rcases seq with as | as
    · dsimp only
      dsimp [seqlike_norm]
      dsimp [List.consOp]
      dsimp [AdHoc.getAt?]
      dsimp [← toGetAt?_eq_toSequence_getAt?]
      dsimp [seqlike_norm]
      simp
    · dsimp only
      dsimp [seqlike_norm]
      dsimp [ωSequence.consOp]
      dsimp [AdHoc.getAt?]
      dsimp [← toGetAt?_eq_toSequence_getAt?]
      dsimp [seqlike_norm]
  consBy_tail := by
    intro a seq i
    rcases seq with as | as
    · dsimp only
      dsimp [seqlike_norm, List.consOp, AdHoc.getAt?, ← toGetAt?_eq_toSequence_getAt?]
    · dsimp only
      dsimp [seqlike_norm, ωSequence.consOp, AdHoc.getAt?, ← toGetAt?_eq_toSequence_getAt?]

def tailOp : TailOp (AdHoc α) α where
  tailBy seq :=
    match seq with
    | .finite as => List.tailOp.tailBy as |> .finite
    | .infinite as => ωSequence.tailOp.tailBy as |> .infinite
  tailBy_cons := by
    intro seq i
    rcases seq with as | as
    · dsimp only
      dsimp [SequenceLike.toGetAt?, AdHoc.getAt?]
      exact List.tailOp.tailBy_cons_at as i
    · dsimp only
      dsimp [SequenceLike.toGetAt?, AdHoc.getAt?]
      exact ωSequence.tailOp.tailBy_cons_at as i

def nilOp : NilOp (AdHoc α) α where
  nilBy := List.nilOp.nilBy |> .finite
  nilBy_empty := List.nilOp.nilBy_empty

def singleOp : SingleOp (AdHoc α) α where
  singleBy a := .finite [a]
  getAt?_zero := by
    intro a
    dsimp [seqlike_norm, AdHoc.getAt?]
    rw [← toGetAt?_eq_toSequence_getAt?]
    dsimp [seqlike_norm]
    rfl
  getAt?_add_on := by
    intro a i
    dsimp [seqlike_norm, AdHoc.getAt?]
    rw [← toGetAt?_eq_toSequence_getAt?]
    dsimp [seqlike_norm]


end AdHoc


end Nemonuri.SequenceLike

end
