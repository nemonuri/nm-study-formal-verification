module

public meta import Nemonuri.SequenceLike.Tactic
public import Nemonuri.SequenceLike.Basic
public import Nemonuri.SequenceProd.Basic

@[expose] public section

namespace Nemonuri

class SequenceProdLike (C: Type _) (α β: outParam <| Type _) where
  fst: SequenceLike.Struct C α
  snd: SequenceLike.Struct C β
  inj {c1 c2: C} : (fst.toGetAt? c1) = (fst.toGetAt? c2) → (snd.toGetAt? c1) = (snd.toGetAt? c2) → c1 = c2


namespace SequenceProdLike

open SequenceProd

variable {C α β: Type _} [SequenceProdLike C α β] {c: C}

def toSequenceProd (c: C) : SequenceProd α β where
  fst := fst.toSequence c
  snd := snd.toSequence c


abbrev toSequenceProdAt (C α β: Type _) [SequenceProdLike C α β] (c: C) : SequenceProd α β := toSequenceProd c

@[defeq]
theorem toSequenceProdAt_eq_toSequenceProd : @toSequenceProdAt C α β _ = @toSequenceProd C α β _ := rfl

theorem toSequenceProdAt_injective : Function.Injective (toSequenceProdAt C α β) := by
  intro c1 c2 lm1
  rewrite [toSequenceProdAt_eq_toSequenceProd] at lm1
  have lm2 := @SequenceProdLike.inj C α β _ c1 c2
  rewrite [SequenceProd.ext_iff] at lm1
  dsimp [toSequenceProd] at lm1
  exact lm2 lm1.left lm1.right

theorem toSequenceProdAt_getAt?_ext {c1 c2: C}
  (req1: (toSequenceProdAt C α β c1).fst.getAt? = (toSequenceProdAt C α β c2).fst.getAt?)
  (req2: (toSequenceProdAt C α β c1).snd.getAt? = (toSequenceProdAt C α β c2).snd.getAt?)
  : c1 = c2 := by
  refine toSequenceProdAt_injective.eq_iff.mp ?_
  refine SequenceProd.ext ?_ ?_
  · exact req1
  · exact req2

instance : CoeOut C (SequenceProd α β) := ⟨toSequenceProd⟩

@[defeq]
theorem fst_toGetAt?_eq_toSequenceProd_fst_getAt? : fst.toGetAt? c = (toSequenceProd c).fst.getAt? := rfl

@[defeq]
theorem snd_toGetAt?_eq_toSequenceProd_snd_getAt? : snd.toGetAt? c = (toSequenceProd c).snd.getAt? := rfl

@[defeq]
theorem fst_toLength?_eq_toSequenceProd_fst_toLength? : fst.toLength? c = (toSequenceProd c).fst.length? := rfl

@[defeq]
theorem snd_toLength?_eq_toSequenceProd_snd_toLength? : snd.toLength? c = (toSequenceProd c).snd.length? := rfl


def toGetAt? (c: C) (i: ℕ) : OptionProd α β := .ofProd? (fst.toGetAt? c i, snd.toGetAt? c i)

@[defeq, seqlike_unfold]
theorem toGetAt?_eq_ofProd?_toGetAt?_at (i: ℕ) : toGetAt? c i = .ofProd? (fst.toGetAt? c i, snd.toGetAt? c i) := rfl

@[seqlike_unfold ←]
theorem toGetAt?_eq_toSequenceProd_getAt? : toGetAt? c = (toSequenceProd c).getAt? := by
  refine funext ?_
  intro i
  rw [toGetAt?_eq_ofProd?_toGetAt?_at]
  rw [SequenceProd.getAt?_eq_ofProd?_getAt?]
  dsimp
  refine congrArg _ ?_
  refine Prod.ext ?_ ?_ <;> dsimp
  · rw [fst_toGetAt?_eq_toSequenceProd_fst_getAt?]
  · rw [snd_toGetAt?_eq_toSequenceProd_snd_getAt?]

attribute [seqlike_unfold] SequenceProdLike.fst SequenceProdLike.snd


end SequenceProdLike

end Nemonuri

end
