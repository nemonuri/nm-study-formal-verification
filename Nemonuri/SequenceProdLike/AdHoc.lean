module

public import Nemonuri.SequenceProdLike.Operations
public import Nemonuri.SequenceLike.AdHoc

@[expose] public section

namespace Nemonuri.SequenceProdLike

structure AdHoc (α β: Type _) where
  fst: SequenceLike.AdHoc α
  snd: SequenceLike.AdHoc β

namespace AdHoc

variable {α β: Type _}

instance toSequenceProdLike : SequenceProdLike (AdHoc α β) α β where
  fst := SequenceLike.Struct.ofSequenceLike _ α |>.contramap AdHoc.fst
  snd := SequenceLike.Struct.ofSequenceLike _ β |>.contramap AdHoc.snd
  inj := by
    rintro ⟨_,_⟩ ⟨_,_⟩ lm1 lm2
    dsimp [SequenceLike.Struct.ofSequenceLike, SequenceLike.Struct.contramap] at lm1 lm2
    replace lm1 := SequenceLike.inj lm1
    replace lm2 := SequenceLike.inj lm2
    rw [lm1, lm2]

/-
def singleFstOp : SingleFstOp (AdHoc α β) α β where
  singleFstBy a := ⟨SequenceLike.AdHoc.consOp.consBy a SequenceLike.AdHoc.nilOp.nilBy, ⟩
-/

end AdHoc

end Nemonuri.SequenceProdLike

end
