module

public import Nemonuri.Sequence.SequenceLike

@[expose] public section

namespace Nemonuri.SequenceLike

open Sequence
--variable (C: Type _) (α: outParam <| Type _)

class Cons (C: Type _) (α: outParam <| Type _) [SequenceLike C α] where
  cons: α → C → C
  cons_head {a: α} {seq: C} : toGetAt? (cons a seq) 0 = .some a
  cons_tail {a: α} {seq: C} {i: ℕ} : toGetAt? (cons a seq) (i + 1) = toGetAt? seq i


namespace Cons

abbrev consAt (C: Type _) {α: Type _} [SequenceLike C α] [Cons C α] (a: α) (seq: C) : C := @cons C α _ _ a seq

abbrev consAt₂ (C α: Type _) [SequenceLike C α] [Cons C α] (a: α) (seq: C) : C := @cons C α _ _ a seq


variable {C: Type _} {α: outParam <| Type _} [SequenceLike C α] [Cons C α]
         {a: α} {seq: C}

@[defeq]
theorem consAt_eq_cons : consAt C a seq = @cons C α _ _ a seq := rfl

@[defeq]
theorem consAt₂_eq_cons : consAt₂ C α a seq = @cons C α _ _ a seq := rfl

theorem cons_head_at (a: α) (seq: C) : toGetAt? (cons a seq) 0 = .some a := @cons_head _ _ _ _ a seq

theorem cons_tail_at (a: α) (seq: C) (i: ℕ) : toGetAt? (cons a seq) (i + 1) = toGetAt? seq i :=
  @cons_tail _ _ _ _ a seq i


theorem cons_toEmptyLabel_eq_nonempty : toEmptyLabel (toSequence <| cons a seq) = .nonempty := by
  let c2 : C := cons a seq
  have lm1 := @length?_le_iff_getAt?_eq_none α c2 0
  have lm2 := cons_head_at a seq
  rw [toGetAt?_eq_toSequence_getAt?] at lm2
  rw [lm2] at lm1
  simp at lm1
  rw [toEmptyLabel_eq_nonempty_iff_length?_ne_zero]
  subst c2
  exact lm1

theorem cons_toFinLabel_eq_infinite_iff_toFinLabel_eq_infinite
  : ((toSequence <| cons a seq).toFinLabel = .infinite) ↔ ((toSequence seq).toFinLabel = .infinite) := by
  have lm1 := cons_tail_at a seq
  constructor
  · intro lm2
    simp [toFinLabel_eq_infinite_iff_forall_getAt?_eq_some] at lm2 ⊢
    intro n
    specialize lm2 (n+1)
    specialize lm1 n
    obtain ⟨a1, lm2⟩ := lm2
    exists a1
    calc
      _ = _ := lm1.symm
      _ = _ := lm2
  · simp [toFinLabel_eq_infinite_iff_forall_getAt?_eq_some]
    intro lm2 n
    rcases n with _ | n
    · have lm3 := @cons_toEmptyLabel_eq_nonempty _ _ _ _ a seq
      simp [toEmptyLabel_eq_nonempty_iff_getAt?_0_eq_some] at lm3
      exact lm3
    · specialize lm1 n
      specialize lm2 n
      obtain ⟨a1, lm2⟩ := lm2
      exists a1
      calc
        _ = _ := lm1
        _ = _ := lm2


theorem cons_toFinLabel_eq_finite_iff_toFinLabel_eq_finite
  : ((toSequence <| cons a seq).toFinLabel = .finite) ↔ ((toSequence seq).toFinLabel = .finite) := by
  have lm1 := @cons_toFinLabel_eq_infinite_iff_toFinLabel_eq_infinite _ _ _ _ a seq
  replace lm1 := Iff.not lm1
  simp [FiniteLabel.ne_infinite_iff_eq_finite] at lm1
  exact lm1



theorem cons_toFinLabel_eq_toFinLabel
  : (toSequence <| cons a seq).toFinLabel = (toSequence seq).toFinLabel := by
  cases lm1: (toSequence seq).toFinLabel
  · exact cons_toFinLabel_eq_finite_iff_toFinLabel_eq_finite.mpr lm1
  · exact cons_toFinLabel_eq_infinite_iff_toFinLabel_eq_infinite.mpr lm1


theorem cons_head?_eq_some
  : (toSequence <| cons a seq).head? = .some a := by
  simp [head?_eq_getElem?, ← getAt?_eq_getElem?]
  exact cons_head

theorem cons_head_eq
  : (toSequence <| cons a seq).head cons_toEmptyLabel_eq_nonempty = a := by
  refine Option.some_inj.mp ?_
  have lm1 := head?_eq_some_head (@cons_toEmptyLabel_eq_nonempty _ _ _ _ a seq)
  rw [← lm1]
  exact cons_head?_eq_some


theorem cons_empty_length_eq_one (req: (toSequence seq).toEmptyLabel = .empty)
  : (toSequence <| cons a seq).length (cons_toFinLabel_eq_toFinLabel.trans (finite_of_empty req)) = 1 := by
  have lm_fin := finite_of_empty req
  have lm_fin2 := (@cons_toFinLabel_eq_toFinLabel _ _ _ _ a _).trans lm_fin
  refine Sequence.length_eq_of_getAt?_isSome_and_add_one_eq_none lm_fin2 ?_ ?_
  · have lm1 := cons_head_at a seq
    rw [← toGetAt?_eq_toSequence_getAt?]
    simp [lm1]
  · rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at req
    specialize req 0
    have lm1 := cons_tail_at a seq 0
    simp [← toGetAt?_eq_toSequence_getAt?] at req lm1 ⊢
    exact lm1.trans req


theorem cons_length_eq_length_add_one (req: (toSequence seq).toFinLabel = .finite)
  : (toSequence <| cons a seq).length (cons_toFinLabel_eq_toFinLabel.trans req) = ((toSequence seq).length req) + 1 := by
  induction lm1: ((toSequence seq).length req) with
  | zero =>
    replace lm1 := length?_eq_zero_of_length_eq_zero lm1
    rw [← toEmptyLabel_eq_empty_iff_length?_eq_zero] at lm1
    exact cons_empty_length_eq_one lm1
  | succ i _ =>
    have lm2 := (@cons_toFinLabel_eq_toFinLabel _ _ _ _ a _).trans req
    have lm3 := cons_tail_at a seq
    simp only [toGetAt?_eq_toSequence_getAt?] at lm3
    refine Sequence.length_eq_of_getAt?_isSome_and_add_one_eq_none lm2 ?_ ?_
    · specialize lm3 i
      have lm4 := Sequence.getAt?_length_sub_one_isSome_iff_nonempty req
      simp [lm1] at lm4
      simp [← lm3] at lm4
      refine lm4.mpr ?_
      refine toEmptyLabel_eq_nonempty_iff_length?_pos.mpr ?_
      rw [length?_eq_natCast_length req]
      rw [← ENat.coe_zero, lm1, ENat.coe_lt_coe]
      exact Trans.trans (Nat.zero_le i) (Nat.lt_add_one i)
    · specialize lm3 (i+1)
      have lm4 := Sequence.getAt?_length_eq_none req
      simp [lm1] at lm4
      exact Eq.trans lm3 lm4


theorem cons_length?_eq_length?_add_one
  : (toSequence <| cons a seq).length? = (toSequence seq).length? + 1 := by
  cases lm1: (toSequence seq).toFinLabel
  · have lm2 := @cons_length_eq_length_add_one _ _ _ _ a _ lm1
    have lm3 := (@cons_toFinLabel_eq_toFinLabel _ _ _ _ a _).trans lm1
    rw [length?_eq_natCast_length lm1, length?_eq_natCast_length lm3]
    rw [lm2]
    simp
  · have lm3 := (@cons_toFinLabel_eq_toFinLabel _ _ _ _ a _).trans lm1
    simp [toFinLabel_eq_infinite_iff_length?_eq_top] at lm1 lm3
    simp [lm1, lm3]

#print cons_length?_eq_length?_add_one


/-
  have lm1 := @cons_tail_at C α _ _
  simp [toGetAt?_eq_toSequence_getAt?] at lm1
  have lm2 := req
  revert lm2
  simp [toFinLabel_eq_finite_iff_length?_eq_natCast]
  intro n lm2
  rewrite [length?_eq_natCast_length req] at lm2
  simp at lm2
  induction n with
  | zero =>
    have lm3 := lm1 a seq 0
-/
/-
  have req2 := (@cons_toFinLabel_eq_toFinLabel C α _ _ a _).trans req
  have lm3 := req2
  revert lm3
  simp [toFinLabel_eq_finite_iff_length?_eq_natCast]
  intro n2 lm3
  rewrite [length?_eq_natCast_length req2] at lm3
  simp at lm3
-/


end Cons


end Nemonuri.SequenceLike

end
