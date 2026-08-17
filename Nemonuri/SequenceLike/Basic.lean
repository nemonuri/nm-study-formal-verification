module

public import Nemonuri.Sequence.Basic

@[expose] public section

namespace Nemonuri

/-- Drop first `n` elements -/
/-
def drop (n : ℕ) (seq: Sequence α) : Sequence α where
  getAt? i := seq.getAt? (i + n)
-/

/-
structure Cons (α: Type _) where
  cons: α → Sequence α → Sequence α
  cons_head {a: α} {seq: Sequence α} : (cons a seq).getAt? 0 = .some a
  cons_tail {a: α} {seq: Sequence α} {i: ℕ} : (cons a seq).getAt? (i + 1) = seq.getAt? i

namespace Cons

variable {cf: Cons α} {a: α} {seq: Sequence α}


/-
theorem cons_length_eq_length_add_one (req: seq.toFiniteLabel = .finite)
  : ((cf.cons a seq).length (cf.cons_finite_iff_finite.mpr req)) = (seq.length req) + 1 := by
  have lm1 := @cf.cons_tail a seq
-/



end Cons

def consBy (a: α) (seq: Sequence α) (f: Cons α) : Sequence α := f.cons a seq




structure Tail (α: Type _) where
  tail: Sequence α → Sequence α
  tail_cons {seq: Sequence α} {i: ℕ} : (tail seq).getAt? i = seq.getAt? (i + 1)

def tailBy (seq: Sequence α) (f: Tail α) : Sequence α := f.tail seq

end Sequence
-/

--[FunLike F α (Option β)]
class SequenceLike (C: Type _) (α: outParam <| Type _) where
  toGetAt? : C → ℕ → (Option α)
  toLength? : C → ℕ∞
  toLength?_toGetAt? {c: C} {i: ℕ} : (i < (toLength? c)) ↔ (toGetAt? c i).isSome
  inj {c1 c2: C} : (toGetAt? c1) = (toGetAt? c2) → c1 = c2



namespace SequenceLike

open Sequence

variable {C: Type _} {α: Type _} [SequenceLike C α] {c: C}

def toSequence (c: C) : Sequence α where
  getAt? i := toGetAt? c i
  length? := toLength? c
  length?_getAt? := @toLength?_toGetAt? C α _ c

abbrev toSequenceAt (C: Type _) (α: Type _) [SequenceLike C α] (c: C) : Sequence α := @toSequence C α _ c

@[defeq]
theorem toSequenceAt_eq_toSequence : @toSequenceAt C α _ = @toSequence C α _ := rfl

theorem toSequenceAt_injective : Function.Injective (toSequenceAt C α) := by
  intro c1 c2 lm1
  rewrite [toSequenceAt_eq_toSequence] at lm1
  have lm2 := @SequenceLike.inj C α _ c1 c2
  refine lm2 ?_
  rewrite [Sequence.ext_iff] at lm1
  dsimp [toSequence] at lm1
  simp [funext_iff] at lm1
  refine funext ?_
  exact lm1

theorem toSequenceAt_getAt?_ext {c1 c2: C} (req: (toSequenceAt C α c1).getAt? = (toSequenceAt C α c2).getAt?)
  : c1 = c2 := by
  refine toSequenceAt_injective.eq_iff.mp ?_
  refine Sequence.ext ?_
  exact req
  --refine @SequenceLike.inj C α _ _

instance : CoeOut C (Sequence α) := ⟨toSequence⟩

@[defeq]
theorem toGetAt?_eq_toSequence_getAt? : toGetAt? c = (toSequence c).getAt? := rfl

@[defeq]
theorem toLength?_eq_toSequence_length? : toLength? c = (toSequence c).length? := rfl

/-
def toEmptyLabel (c: C) : EmptyLabel := .ofENat (toLength? c)

def toFiniteLabel (c: C) : FiniteLabel := .ofENat (toLength? c)

@[defeq]
theorem toEmptyLabel_eq_toSequence_toEmptyLabel : toEmptyLabel c = (toSequence c).toEmptyLabel := rfl

@[defeq]
theorem toFiniteLabel_eq_toSequence_toFiniteLabel : toFiniteLabel c = (toSequence c).toFiniteLabel := rfl
-/

def toGetAt (c: C) (i: ℕ) (req: i < toLength? c) : α :=
  (toGetAt? c i).get ((@toLength?_eq_toSequence_length? C α _ c) ▸ req |> (Sequence.length?_getAt? _).mp)

@[defeq]
theorem toGetAt_eq_toSequence_getAt : (toGetAt c) = ((toSequence c).getAt) := rfl

instance (priority := low) ofSequence : SequenceLike (Sequence α) α :=
  .mk Sequence.getAt? Sequence.length? (fun {seq} => Sequence.length?_getAt? seq) Sequence.ext

end SequenceLike




end Nemonuri

end
