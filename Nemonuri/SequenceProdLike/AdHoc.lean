module

public import Nemonuri.SequenceProdLike.Operations
public import Nemonuri.SequenceLike.AdHoc

@[expose] public section

namespace Nemonuri.SequenceProdLike

open SequenceLike
open SequenceLike renaming AdHoc → SeqAdHoc


structure AdHoc (α β: Type _) where
  fst: SeqAdHoc α
  snd: SeqAdHoc β



namespace AdHoc

variable {α β: Type _}

instance toSequenceProdLike : SequenceProdLike (AdHoc α β) α β where
  fst := Struct.ofSequenceLike _ α |>.contramap AdHoc.fst
  snd := Struct.ofSequenceLike _ β |>.contramap AdHoc.snd
  inj := by
    rintro ⟨_,_⟩ ⟨_,_⟩ lm1 lm2
    dsimp [Struct.ofSequenceLike, Struct.contramap] at lm1 lm2
    replace lm1 := SequenceLike.inj lm1
    replace lm2 := SequenceLike.inj lm2
    rw [lm1, lm2]



def singleFstOp : SingleFstOp (AdHoc α β) α β where
  singleFstBy a := ⟨SeqAdHoc.singleOp.singleBy a, SeqAdHoc.nilOp.nilBy⟩
  getAt?_zero := by
    intro a
    simp [seqlike_unfold]
    refine OptionProd.ext ?_ ?_ <;> simp
    . exact SeqAdHoc.singleOp.getAt?_zero
    · rfl
  getAt?_add_one := by
    intro a i
    simp [seqlike_unfold]
    refine OptionProd.ext ?_ ?_ <;> simp
    · exact SeqAdHoc.singleOp.getAt?_add_one
    · rfl

def stepLOp : StepLOp (AdHoc α β) α β where
  stepLBy a b sp := ⟨SeqAdHoc.consOp.consBy a sp.fst, SeqAdHoc.consOp.consBy b sp.snd⟩
  getAt?_zero := by
    intro a b sp
    simp [seqlike_unfold]
    refine OptionProd.ext ?_ ?_ <;>
    (simp; exact SeqAdHoc.consOp.consBy_head)
  getAt?_add_one := by
    intro a b sp i
    simp [seqlike_unfold]
    refine OptionProd.ext ?_ ?_ <;>
    (simp; exact SeqAdHoc.consOp.consBy_tail)




end AdHoc

end Nemonuri.SequenceProdLike

end
