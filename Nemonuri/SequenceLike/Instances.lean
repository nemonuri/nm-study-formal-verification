module

public import Nemonuri.SequenceLike
public import Nemonuri.SequenceLike.Operations
public import Cslib.Foundations.Data.OmegaSequence.Init

@[expose] public section

namespace Nemonuri.SequenceLike

open Cslib

variable {α: Type _}

scoped instance ofList : SequenceLike (List α) α where
  toGetAt? as i := as[i]?
  toLength? as := as.length
  toLength?_toGetAt? := by
    intro as i
    simp
  inj := by
    intro as1 as2 lm1
    simp [funext_iff] at lm1
    exact List.ext_getElem? lm1

section OfList

def consList : ConsOp (List α) α where
  consBy a as := a::as
  consBy_head := by dsimp [toGetAt?]; simp
  consBy_tail := by
    intro _ _ _
    dsimp [toGetAt?]

def tailList : TailOp (List α) α where
  tailBy as := as.tail
  tailBy_cons := by
    intro _ _
    dsimp [toGetAt?]
    simp only [List.getElem?_tail]

def nilList : NilOp (List α) α where
  nilBy := []
  nilBy_empty := by
    dsimp [toSequence, toLength?, Sequence.toEmptyLabel]
    exact EmptyLabel.ofENat_zero

end OfList


scoped instance ofωSequence : SequenceLike (ωSequence α) α where
  toGetAt? as i := as i |> .some
  toLength? as := ⊤
  toLength?_toGetAt? := by
    intro as i
    simp
  inj := by
    intro c1 c2 lm1
    simp [funext_iff] at lm1
    exact ωSequence.ext lm1


section OfωSequence

open scoped ωSequence

def consωSeq : ConsOp (ωSequence α) α where
  consBy a as := a ::ω as
  consBy_head := by
    intro _ _
    dsimp [toGetAt?]
  consBy_tail := by
    intro _ _ _
    dsimp [toGetAt?]

def tailωSeq : TailOp (ωSequence α) α where
  tailBy as := as.tail
  tailBy_cons := by
    intro _ _
    dsimp [toGetAt?]

end OfωSequence



end Nemonuri.SequenceLike

end
