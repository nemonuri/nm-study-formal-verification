module

public import Nemonuri.Sequence.SequenceLike
public import Nemonuri.Sequence.Operations
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

def consList : ConsBy (List α) α where
  consBy a as := a::as
  consBy_head := by dsimp [toGetAt?]; simp
  consBy_tail := by
    intro _ _ _
    dsimp [toGetAt?]

def tailList : TailBy (List α) α where
  tailBy as := as.tail
  tailBy_cons := by
    intro as i
    --have lm1 := @SequenceLike.inj (List α) α _ as as.tail
    --dsimp [toGetAt?] at lm1 ⊢
    --simp [funext_iff] at lm1
    dsimp [toGetAt?]
    cases lm1: compare i as.length <;> dsimp [Ord.compare] at lm1
    · simp at lm1
      have lm2 := as.length_tail
      simp [lm1]
      --simp [lm1]
      --have lm2 := as.somee
/-
    induction as with
    | nil => simp
    | cons a as lm2 =>
      simp
-/
      --simp only [List.getElem?_cons_succ, List.tail_cons] at lm1
      --obtain ⟨a1, lm1⟩ := lm1
/-
    dsimp [toGetAt?]
    by_cases lm1: as[i]?.isNone
    · simp at lm1
      simp [lm1]
      rcases i with _ | i
      · simp
        calc
          _ ≤ _ := lm1
          _ ≤ _ := Nat.zero_le 1
      · simpa using lm1
    · have lm7 := lm1
      by_cases lm2: as[i+1]?.isNone
      · have lm6 := lm2
        simp at lm6
        simp only [← Bool.not_eq, Option.not_isNone, Option.isSome_iff_exists] at lm7
        revert lm7; simp [List.getElem?_eq_some_iff] ; intro lm7
        rewrite [Option.isNone_iff_eq_none] at lm2
        induction i with
        | zero =>
          dsimp at lm2 lm6 ⊢
          have lm8 := as.getelem?some

        --have ⟨lm8, lm9⟩ := List.getElem?_eq_some_iff.mp lm7
-/
/-
        cases lm3: as with
        | nil => simp
        | cons a as2 =>
          simp at lm1 lm2
          have lm4 := Nat.eq_iff_le_and_ge.mpr (And.intro lm2 lm1)
          simp only [← lm3]
          simp [lm4]
-/
          --simp [lm3]

/-
      have lm4 := lm1
      simp at lm1
      by_cases lm2: as.length ≤ 1
      · have lm3 := Trans.trans lm1 lm2
        simp at lm3
        subst lm3
        rw [Nat.lt_iff_add_one_le] at lm1
        have lm5 := Nat.eq_iff_le_and_ge.mpr (And.intro lm2 lm1)
        clear lm1 lm2
-/
/-
      simp [lm1]
      induction i with
      | zero =>
        simp
-/
/-
    have lm1 := @as.getElem?_eq_some_iff _
    have lm2 i := @as.tail.getElem?_eq_none_iff _ i
    induction lm3: as with
    | nil => simp
    | cons a as2 lm4 =>
      induction lm5: as.tail with
      | nil =>
        simp [lm3] at lm5
        simp [lm5]
        intro cont
-/
/-
      specialize lm1 a
      simp [← lm3]
      have := List.getelem?getel
-/
/-
    have lm1 := @as.tail.getElem?_eq_some_iff _ i
    have lm2 := @as.tail.getElem?_eq_none_iff _ i
    induction lm3: as.tail with
    | nil =>
      induction lm4: as with
      | nil => simp
      | cons a as2 _ =>
-/
        --conv at lm2 =>
          --conv => lhs; rw [lm3]; simp
          --conv => rhs; rw [lm3];




/-
      rcases as with _ | ⟨a, as⟩
      · simp
      · simp at lm2
        simp [lm2]
-/
    --| cons a as2 =>
    --  simp only [List.tail_cons]

/-
    have lm1 := @toLength?_toGetAt? (List α) α _ as i
    dsimp [toLength?] at lm1
    dsimp [toGetAt?] at lm1 ⊢
    simp only [ENat.coe_lt_coe] at lm1
    rw [List.getElem?_tail]

    replace lm1 := Iff.not lm1
-/
      --clear lm1
      --simp at lm2 ⊢
    --simp [SequenceLike.toGetAt?_eq_toSequence_getAt?] at lm1 ⊢
    --have lm2 :=
    --simp only [SequenceLike.toGetAt?_eq_toSequence_getAt?]
    --dsimp [toGetAt?]
    --simp


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





end Nemonuri.SequenceLike

end
