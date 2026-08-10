module

public import Nemonuri.Sequence.Instances

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
      simp [← toGetAt?_eq_toSequence_getAt?, toGetAt?] at lm1
  · split at lm1 <;> rename_i seq2 as2
    · specialize lm1 as2.length
      simp [← toGetAt?_eq_toSequence_getAt?, toGetAt?] at lm1
    · congr
      refine toSequenceAt_getAt?_ext ?_
      exact funext lm1

end AdHoc




instance ofAdHoc : SequenceLike (AdHoc α) α where
  toGetAt? := AdHoc.getAt?
  toLength? := AdHoc.length?
  toLength?_toGetAt? {_ _} := by
    dsimp [AdHoc.getAt?, AdHoc.length?]
    split <;> (
      dsimp [← toLength?_eq_toSequence_length?, ← toGetAt?_eq_toSequence_getAt?]
      exact toLength?_toGetAt? )
  inj := AdHoc.getAt?_injective.eq_iff.mp




end Nemonuri.SequenceLike

end
