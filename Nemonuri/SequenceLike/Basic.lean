module

public import Nemonuri.Sequence.Basic

@[expose] public section

namespace Nemonuri


structure SequenceLike.Struct (C α: Type _)  where
  toGetAt? : C → ℕ → (Option α)
  toLength? : C → ℕ∞
  toLength?_toGetAt? {c: C} {i: ℕ} : (i < (toLength? c)) ↔ (toGetAt? c i).isSome

class SequenceLike (C: Type _) (α: outParam <| Type _) where
  toSturct: SequenceLike.Struct C α
  inj {c1 c2: C} : (toSturct.toGetAt? c1) = (toSturct.toGetAt? c2) → c1 = c2



namespace SequenceLike

open Sequence

variable {C: Type _} {α: Type _} [SequenceLike C α] {c: C}

def toGetAt? : C → ℕ → (Option α) := toSturct.toGetAt?

def toLength? : C → ℕ∞ := toSturct.toLength?

theorem toLength?_toGetAt? {c: C} {i: ℕ} : (i < (toLength? c)) ↔ (toGetAt? c i).isSome := by
  have lm1 := @toSturct.toLength?_toGetAt? c i
  dsimp [toGetAt?, toLength?]
  exact lm1

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


def toGetAt (c: C) (i: ℕ) (req: i < toLength? c) : α :=
  (toGetAt? c i).get ((@toLength?_eq_toSequence_length? C α _ c) ▸ req |> (Sequence.length?_getAt? _).mp)

@[defeq]
theorem toGetAt_eq_toSequence_getAt : (toGetAt c) = ((toSequence c).getAt) := rfl

instance (priority := low) ofSequence : SequenceLike (Sequence α) α :=
  .mk (.mk Sequence.getAt? Sequence.length? (fun {seq} => Sequence.length?_getAt? seq)) Sequence.ext


theorem toLength?_ne_top_iff_toSequence_finite : (toLength? c ≠ ⊤) ↔ (toSequence c).toFiniteLabel = .finite := by
  rw [toLength?_eq_toSequence_length?]
  rw [finite_iff_length?_ne_top]

end SequenceLike




end Nemonuri

end
