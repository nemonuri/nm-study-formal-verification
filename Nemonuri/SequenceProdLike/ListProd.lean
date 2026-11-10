module

public import Nemonuri.SequenceProdLike.Operations
public import Nemonuri.SequenceLike.Instances

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.SequenceProdLike

structure ListProd (α β: Type*) where
  fst : List α
  snd : List β

namespace ListProd

variable {α β: Type*}

open Nemonuri.SequenceLike in
instance sequenceProdLike : SequenceProdLike (ListProd α β) α β where
  fst := Struct.ofSequenceLike _ α |>.contramap ListProd.fst
  snd := Struct.ofSequenceLike _ β |>.contramap ListProd.snd
  inj := by
    rintro ⟨_, _⟩ ⟨_, _⟩ lm1 lm2
    dsimp [Struct.ofSequenceLike, Struct.contramap] at lm1 lm2
    replace lm1 := SequenceLike.inj lm1
    replace lm2 := SequenceLike.inj lm2
    rw [lm1, lm2]


def singleFstOp : SingleFstOp (ListProd α β) α β where
  singleFstBy a := ⟨[a], []⟩
  getAt?_zero := by
    intro a
    simp [seqlike_unfold]
    dsimp [OptionProd.ofProd?]
  getAt?_add_one := by
    intro a i
    simp [seqlike_unfold]
    dsimp [OptionProd.ofProd?]

def stepLOp : StepLOp (ListProd α β) α β where
  stepLBy a b sp := ⟨a :: sp.fst, b :: sp.snd⟩
  getAt?_zero := by
    intro a b sp
    simp [seqlike_unfold]
    dsimp [OptionProd.ofProd?]
  getAt?_add_one := by
    intro a b sp i
    simp [seqlike_unfold]


end ListProd


end Nemonuri.SequenceProdLike

end
