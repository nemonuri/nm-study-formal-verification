module

public import Nemonuri.Sequence.SequenceLike
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





end Nemonuri.SequenceLike

end
