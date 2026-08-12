module

public import Nemonuri.Sequence.SequenceLike

@[expose] public section

namespace Nemonuri.Sequence

variable {α: Type _} {seq: Sequence α}

def cons (a: α) (seq: Sequence α) : Sequence α where
  getAt? i :=
    match i with
    | 0 => .some a
    | i + 1 => seq.getAt? i
  length? := seq.length? + 1
  length?_getAt? := by
    intro i
    split
    · simp
    · rename_i _ i
      have lm1 := @seq.length?_getAt? i
      refine Iff.trans ?_ lm1
      simp

def tail (seq: Sequence α) : Sequence α where
  getAt? i := seq.getAt? (i + 1)
  length? := seq.length? - 1
  length?_getAt? := by
    intro i
    cases lm2: seq.length?
    · rewrite [← toFinLabel_eq_infinite_iff_length?_eq_top, toFinLabel_eq_infinite_iff_forall_getAt?_eq_some] at lm2
      specialize lm2 (i+1)
      rewrite [← Option.isSome_iff_exists] at lm2
      simpa using lm2
    · rename ℕ => len
      cases len with
      | zero =>
        simp
        have lm3 :=
          lm2
          |> toEmptyLabel_eq_empty_iff_length?_eq_zero.mpr
          |> toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none.mp
        exact lm3 (i+1)
      | succ len =>
        conv =>
          lhs
          conv =>
            arg 2
            arg 2
            rw [← ENat.coe_one]
          conv =>
            arg 2
            rw [← ENat.coe_sub]
          rw [ENat.coe_lt_coe]
          dsimp only [Nat.add_one_sub_one]
        have ⟨lm4, lm5⟩ := length?_eq_natCast_iff_length_eq.mp lm2
        have lm6 := getAt?_length_sub_one_isSome_iff_nonempty lm4
        simp [lm5] at lm6
        by_cases lm7: len = i + 1
        · simp [lm7] at lm6 ⊢
          refine lm6.mpr ?_
          rw [toEmptyLabel_eq_nonempty_iff_length?_ne_zero]
          rw [lm2]
          simp
        · have lm8 := @lt_length_iff_getAt?_isSome _  _ lm4 (i+1)
          refine Iff.trans ?_ lm8
          rw [lm5]
          simp

def nil : Sequence α where
  getAt? _ := .none
  length? := 0
  length?_getAt? := by
    intro _; simp

def takeRec (n: ℕ) (seq: Sequence α) : Sequence α :=
  match n with
  | 0 => nil
  | n + 1 =>
    if lm1: seq.toEmptyLabel = .empty then
      seq
    else
      cons (seq.head (EmptyLabel.ne_empty_iff_eq_nonempty.mp lm1)) (takeRec n seq.tail)

def take (n: ℕ) (seq: Sequence α) : Sequence α where
  getAt? i :=
    if lm1: i < n then
      seq.getAt? i
    else
      .none
  length? := if seq.length? < n then seq.length? else Nat.cast n
  length?_getAt? := by
    intro i
    split <;> split <;> rename_i lm1 lm2
    · exact seq.length?_getAt?
    · simp at lm2 ⊢
      rw [← ENat.coe_le_coe] at lm2
      apply le_of_lt
      calc
       _ < _ := lm1
       _ ≤ _ := lm2
    · simp [lm2]
      simp at lm1
      refine @seq.length?_getAt? i |>.mp ?_
      rw [← ENat.coe_lt_coe] at lm2
      calc
        _ < _ := lm2
        _ ≤ _ := lm1
    · simpa using lm2

/-
theorem takeRec_eq_take : @takeRec = @take := by
  ext α n seq
  induction n with
  | zero =>
    refine Sequence.ext ?_
    unfold takeRec
    dsimp [take]
    dsimp [nil]
  | succ n lm1 =>
    refine Sequence.ext ?_
    unfold takeRec
    dsimp [take]
    refine funext ?_
    intro i
    split <;> split <;> rename_i lm2 lm3
    · rfl
    · rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm2
      exact lm2 i
    · dsimp [cons]
      split
      · simp only [EmptyLabel.ne_empty_iff_eq_nonempty] at lm2
        replace lm2 := seq.head?_eq_some_head lm2 |>.symm
        rewrite [head?_eq_getAt?_zero] at lm2
        exact lm2
      · rename_i i
        simp only [EmptyLabel.ne_empty_iff_eq_nonempty] at lm2
-/
        --rewrite [← Sequence.ext_iff, funext_iff] at lm1
        --refine Eq.trans ?_ (lm1 _)
/-
    rewrite [← Sequence.ext_iff] at lm1
    revert lm1
    dsimp [take]
    intro lm1
    unfold takeRec
    split
-/
    --have lm1 := Sequence.lengtheqof
    --unfold takeRec
    --dsimp [take]


def append (seq1: Sequence α) (req: seq1.toFinLabel = .finite) (seq2: Sequence α) : Sequence α where
  getAt? i :=
    if lm1: i < seq1.length req then
      seq1.getAt? i
    else
      seq2.getAt? (i - seq1.length req)
  length? := seq1.length req + seq2.length?
  length?_getAt? := by
    intro i
    split <;> rename_i lm1
    · refine Iff.trans (iff_true_intro ?_) ?_
      · calc
          _ < _ := ENat.coe_lt_coe.mpr lm1
          _ ≤ _ := by simp only [self_le_add_right]
      · rw [true_iff]
        have lm2 := lt_length_iff_getAt?_isSome_at req i
        exact lm2.mp lm1
    · cases lm2: seq2.toFinLabel
      · have lm3 := seq2.length?_eq_natCast_length lm2
        conv =>
          lhs
          rw [lm3, ← ENat.coe_add, ENat.coe_lt_coe]
        have lm4 := lt_length_iff_getAt?_isSome_at req i
        have lm5 := lt_length_iff_getAt?_isSome_at lm2 (i - seq1.length req)
        refine Iff.trans ?_ lm5
        symm
        refine Nat.sub_lt_iff_lt_add' ?_
        simpa using lm1
      · have lm3 := toFinLabel_eq_infinite_iff_length?_eq_top.mp lm2
        have lm4 := @seq2.length?_getAt?
        simp [lm3] at lm4 ⊢
        exact @lm4 _



end Nemonuri.Sequence

namespace Nemonuri.SequenceLike

open Sequence

structure ConsOp (C: Type _) (α: Type _) [SequenceLike C α] where
  consBy: α → C → C
  consBy_head {a: α} {seq: C} : toGetAt? (consBy a seq) 0 = .some a
  consBy_tail {a: α} {seq: C} {i: ℕ} : toGetAt? (consBy a seq) (i + 1) = toGetAt? seq i


namespace ConsOp


variable {C: Type _} {α: Type _} [SequenceLike C α]
         {cb: ConsOp C α} {a: α} {seq: C}


theorem consBy_head_at (a: α) (seq: C) : toGetAt? (cb.consBy a seq) 0 = .some a := @cb.consBy_head _ a seq

theorem consBy_tail_at (a: α) (seq: C) (i: ℕ) : toGetAt? (cb.consBy a seq) (i + 1) = toGetAt? seq i :=
  @cb.consBy_tail _ a seq i



theorem consBy_toEmptyLabel_eq_nonempty : toEmptyLabel (cb.consBy a seq : Sequence α) = .nonempty := by
  let c2 : C := cb.consBy a seq
  have lm1 := @length?_le_iff_getAt?_eq_none α c2 0
  have lm2 := cb.consBy_head_at a seq
  rw [toGetAt?_eq_toSequence_getAt?] at lm2
  rw [lm2] at lm1
  simp at lm1
  rw [toEmptyLabel_eq_nonempty_iff_length?_ne_zero]
  subst c2
  exact lm1

theorem consBy_toEmptyLabel_eq_nonempty_at (a: α) (seq: C) : toEmptyLabel (cb.consBy a seq : Sequence α) = .nonempty :=
  @cb.consBy_toEmptyLabel_eq_nonempty _ _ _ a seq

theorem consBy_toFinLabel_eq_infinite_iff_toFinLabel_eq_infinite
  : ((cb.consBy a seq : Sequence α).toFinLabel = .infinite) ↔ ((seq : Sequence α).toFinLabel = .infinite) := by
  have lm1 := cb.consBy_tail_at a seq
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
    · have lm3 := cb.consBy_toEmptyLabel_eq_nonempty_at a seq
      simp [toEmptyLabel_eq_nonempty_iff_getAt?_0_eq_some] at lm3
      exact lm3
    · specialize lm1 n
      specialize lm2 n
      obtain ⟨a1, lm2⟩ := lm2
      exists a1
      calc
        _ = _ := lm1
        _ = _ := lm2


theorem consBy_toFinLabel_eq_finite_iff_toFinLabel_eq_finite
  : ((cb.consBy a seq : Sequence α).toFinLabel = .finite) ↔ ((seq : Sequence α).toFinLabel = .finite) := by
  have lm1 := @cb.consBy_toFinLabel_eq_infinite_iff_toFinLabel_eq_infinite _ _ _ a seq
  replace lm1 := Iff.not lm1
  simp [FiniteLabel.ne_infinite_iff_eq_finite] at lm1
  exact lm1



theorem consBy_toFinLabel_eq_toFinLabel
  : (cb.consBy a seq : Sequence α).toFinLabel = (seq : Sequence α).toFinLabel := by
  cases lm1: (toSequence seq).toFinLabel
  · exact cb.consBy_toFinLabel_eq_finite_iff_toFinLabel_eq_finite.mpr lm1
  · exact cb.consBy_toFinLabel_eq_infinite_iff_toFinLabel_eq_infinite.mpr lm1

theorem consBy_toFinLabel_eq_toFinLabel_at (a: α) (seq: C)
  : (cb.consBy a seq : Sequence α).toFinLabel = (seq : Sequence α).toFinLabel :=
  @cb.consBy_toFinLabel_eq_toFinLabel _ _ _ a seq


theorem consBy_head?_eq_some
  : (cb.consBy a seq : Sequence α).head? = .some a := by
  simp [head?_eq_getElem?, ← getAt?_eq_getElem?]
  exact cb.consBy_head


theorem consBy_head_eq
  : (cb.consBy a seq : Sequence α).head cb.consBy_toEmptyLabel_eq_nonempty = a := by
  refine Option.some_inj.mp ?_
  have lm1 := head?_eq_some_head (cb.consBy_toEmptyLabel_eq_nonempty_at a seq)
  rw [← lm1]
  exact cb.consBy_head?_eq_some


theorem consBy_empty_length_eq_one (req: (seq : Sequence α).toEmptyLabel = .empty)
  : (cb.consBy a seq : Sequence α).length (cb.consBy_toFinLabel_eq_toFinLabel.trans (finite_of_empty req)) = 1 := by
  have lm_fin := finite_of_empty req
  have lm_fin2 := (cb.consBy_toFinLabel_eq_toFinLabel_at a _).trans lm_fin
  refine Sequence.length_eq_of_getAt?_isSome_and_add_one_eq_none lm_fin2 ?_ ?_
  · have lm1 := cb.consBy_head_at a seq
    rw [← toGetAt?_eq_toSequence_getAt?]
    simp [lm1]
  · rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at req
    specialize req 0
    have lm1 := cb.consBy_tail_at a seq 0
    simp [← toGetAt?_eq_toSequence_getAt?] at req lm1 ⊢
    exact lm1.trans req


theorem consBy_length_eq_length_add_one (req: (seq : Sequence α).toFinLabel = .finite)
  : (cb.consBy a seq : Sequence α).length (cb.consBy_toFinLabel_eq_toFinLabel.trans req) = ((seq : Sequence α).length req) + 1 := by
  induction lm1: ((toSequence seq).length req) with
  | zero =>
    replace lm1 := length?_eq_zero_of_length_eq_zero lm1
    rw [← toEmptyLabel_eq_empty_iff_length?_eq_zero] at lm1
    exact cb.consBy_empty_length_eq_one lm1
  | succ i _ =>
    have lm2 := (cb.consBy_toFinLabel_eq_toFinLabel_at a _).trans req
    have lm3 := cb.consBy_tail_at a seq
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


theorem consBy_length?_eq_length?_add_one
  : (cb.consBy a seq : Sequence α).length? = (seq : Sequence α).length? + 1 := by
  cases lm1: (toSequence seq).toFinLabel
  · have lm2 := @cb.consBy_length_eq_length_add_one _ _ _ a _ lm1
    have lm3 := (cb.consBy_toFinLabel_eq_toFinLabel_at a _).trans lm1
    rw [length?_eq_natCast_length lm1, length?_eq_natCast_length lm3]
    rw [lm2]
    simp
  · have lm3 := (cb.consBy_toFinLabel_eq_toFinLabel_at a _).trans lm1
    simp [toFinLabel_eq_infinite_iff_length?_eq_top] at lm1 lm3
    simp [lm1, lm3]


end ConsOp


structure TailOp (C: Type _) (α: Type _) [SequenceLike C α] where
  tailBy: C → C
  tailBy_cons {seq: C} {i: ℕ} : toGetAt? (tailBy seq) i = toGetAt? seq (i + 1)

namespace TailOp

variable {C: Type _} {α: Type _} [SequenceLike C α]
         {tb: TailOp C α} {seq: C}

theorem tailBy_cons_at (seq: C) (i: ℕ) : toGetAt? (tb.tailBy seq) i = toGetAt? seq (i + 1) := @tb.tailBy_cons seq i


theorem tailBy_infinite_iff_infinite
  : (tb.tailBy seq : Sequence α).toFinLabel = .infinite ↔ (seq : Sequence α).toFinLabel = .infinite := by
  have lm1 := tb.tailBy_cons_at seq
  simp only [toGetAt?_eq_toSequence_getAt?] at lm1
  simp [toFinLabel_eq_infinite_iff_forall_getAt?_eq_some]
  refine not_iff_not.mp ?_
  simp [← Option.eq_none_iff_forall_ne_some]
  constructor
  · rintro ⟨n, lm2⟩
    specialize lm1 n
    rewrite [lm2] at lm1
    exact Exists.intro (n+1) lm1.symm
  · rintro ⟨n, lm2⟩
    induction n with
    | zero =>
      specialize lm1 0
      replace lm2 := add_one_getAt?_none_of_getAt?_none lm2
      exists 0
      calc
        _ = _ := lm1
        _ = _ := lm2
    | succ n _ =>
      specialize lm1 n
      simp [← lm1] at lm2
      exists n

theorem tailBy_toFinLabel_eq_toFinLabel
  : (tb.tailBy seq : Sequence α).toFinLabel = (seq : Sequence α).toFinLabel := by
  cases lm1: (toSequence seq).toFinLabel
  · have lm2 := Iff.not (@tb.tailBy_infinite_iff_infinite _ _ _ seq)
    simp only [FiniteLabel.ne_infinite_iff_eq_finite] at lm2
    simpa [lm1] using lm2
  · exact tb.tailBy_infinite_iff_infinite.mpr lm1

theorem tailBy_toFinLabel_eq_toFinLabel_at (seq: C) : (tb.tailBy seq : Sequence α).toFinLabel = (seq : Sequence α).toFinLabel :=
  @tb.tailBy_toFinLabel_eq_toFinLabel _ _ _ seq


protected theorem eq_zero_of_forall_eq_add_one {α: Sort _} (P: ℕ → α) (req: ∀(i: ℕ), P i = P (i + 1)) (i: ℕ) : P i = P 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    specialize req i
    exact req.symm.trans ih


theorem tailBy_fixpoint_iff_empty (req: (seq : Sequence α).toFinLabel = .finite)
  : (tb.tailBy seq = seq) ↔ ((seq : Sequence α).toEmptyLabel = .empty) := by
  have lm1 := tb.tailBy_cons_at seq
  constructor
  · intro lm2
    simp [lm2, toGetAt?_eq_toSequence_getAt?] at lm1
    rewrite [toFinLabel_eq_finite_iff_exists_getAt?_eq_none] at req
    obtain ⟨n, req⟩ := req
    rw [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none]
    intro n2
    have lm3 := TailOp.eq_zero_of_forall_eq_add_one _ lm1 n
    have lm4 := TailOp.eq_zero_of_forall_eq_add_one _ lm1 n2
    calc
      _ = _ := lm4
      _ = _ := lm3.symm
      _ = _ := req
  · intro lm2
    refine toSequenceAt_getAt?_ext ?_
    refine funext ?_
    intro n
    specialize lm1 n
    simp [toGetAt?_eq_toSequence_getAt?] at lm1
    rw [lm1]
    rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm2
    calc
      _ = _ := lm2 (n+1)
      _ = _ := (lm2 n).symm


theorem tailBy_fixpoint_iff_const_eq (req: (seq : Sequence α).toFinLabel = .infinite)
  : (tb.tailBy seq = seq) ↔ (∃(a: α), (Function.const ℕ (.some a)) = (seq : Sequence α).getAt?) := by
  have lm1 := tb.tailBy_cons_at seq
  simp [toGetAt?_eq_toSequence_getAt?] at lm1
  simp [toFinLabel_eq_infinite_iff_forall_getAt?_eq_some] at req
  constructor
  · intro lm2
    simp [lm2] at lm1
    replace lm1 := fun i => TailOp.eq_zero_of_forall_eq_add_one _ lm1 i
    obtain ⟨a0, lm3⟩ := req 0
    exists a0
    refine funext ?_
    intro n2
    simp
    specialize lm1 n2
    exact lm1.trans lm3 |>.symm
  · rintro ⟨a2, lm2⟩
    refine toSequenceAt_getAt?_ext ?_
    refine funext ?_
    intro n
    have lm3 := lm1 n
    rw [lm3]; clear lm3
    simp only [funext_iff, Function.const_apply] at lm2
    calc
      _ = _ := lm2 (n+1) |>.symm
      _ = _ := lm2 n

theorem tailBy_empty_of_empty (req: (seq : Sequence α).toEmptyLabel = .empty)
  : (tb.tailBy seq : Sequence α).toEmptyLabel = .empty := by
  have lm1 := finite_of_empty req
  have lm2 := tb.tailBy_fixpoint_iff_empty lm1 |>.mpr req
  rw [lm2]
  exact req

theorem nonempty_iff_length_eq_one (req: (tb.tailBy seq : Sequence α).toEmptyLabel = .empty)
  : ((seq : Sequence α).toEmptyLabel = .nonempty) ↔ ((seq : Sequence α).length (tb.tailBy_toFinLabel_eq_toFinLabel.symm.trans (finite_of_empty req)) = 1) := by
  have lm1 := tb.tailBy_toFinLabel_eq_toFinLabel.symm.trans (finite_of_empty req)
  constructor
  · intro lm2
    have lm3 := tb.tailBy_cons_at seq
    refine Sequence.length_eq_of_getAt?_isSome_and_add_one_eq_none lm1 ?_ ?_
    · rw [toEmptyLabel_eq_nonempty_iff_getAt?_0_eq_some] at lm2
      simpa [Option.isSome_iff_exists] using lm2
    · rw [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at req
      specialize req 0
      specialize lm3 0
      simp [toGetAt?_eq_toSequence_getAt?] at lm3
      dsimp
      calc
        _ = _ := lm3.symm
        _ = _ := req
  · intro lm2
    rewrite [← ENat.coe_inj, ← length?_eq_natCast_length] at lm2
    rw [toEmptyLabel_eq_nonempty_iff_length?_ne_zero, lm2]
    simp


theorem tailBy_empty_of_length?_eq_one (req: (seq: Sequence α).length? = 1)
  : (tb.tailBy seq : Sequence α).toEmptyLabel = .empty := by
  have lm1 := tb.tailBy_cons_at seq
  simp only [toGetAt?_eq_toSequence_getAt?] at lm1
  rewrite [← ENat.coe_one] at req
  have ⟨lm2, lm3⟩ := length?_eq_natCast_iff_length_eq.mp req
  have lm4 := lm3 ▸ (getAt?_length_eq_none lm2)
  specialize lm1 0
  dsimp at lm1
  refine toEmptyLabel_eq_empty_iff_getAt?_0_eq_none.mpr ?_
  exact lm1.trans lm4


theorem not_tailBy_nonempty_and_empty
  (req1: (tb.tailBy seq : Sequence α).toEmptyLabel = .nonempty) (req2: (seq : Sequence α).toEmptyLabel = .empty) : False := by
  rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at req2
  rewrite [toEmptyLabel_eq_nonempty_iff_exists_getAt?_eq_some] at req1
  obtain ⟨n, a, lm1⟩ := req1
  specialize req2 (n+1)
  have lm2 := tb.tailBy_cons_at seq n
  simp [toGetAt?_eq_toSequence_getAt?] at lm2
  simp [req2, lm1] at lm2



theorem tailBy_length_eq_length_sub_one (req: (seq : Sequence α).toFinLabel = .finite)
  : (tb.tailBy seq : Sequence α).length (tb.tailBy_toFinLabel_eq_toFinLabel.trans req) = (seq : Sequence α).length req - 1 := by
  cases lm1: (tb.tailBy seq : Sequence α).toEmptyLabel <;>
  cases lm2: (seq : Sequence α).toEmptyLabel
  · replace lm1 := length_eq_zero_of_empty lm1
    replace lm2 := length_eq_zero_of_empty lm2
    rw [lm1, lm2]
  · have lm3 := tb.nonempty_iff_length_eq_one lm1 |>.mp lm2
    replace lm1 := length_eq_zero_of_empty lm1
    rw [lm1, lm3]
  · have lm3 := tb.not_tailBy_nonempty_and_empty lm1 lm2
    exact False.elim lm3
  · have lm3 := tb.tailBy_cons_at seq
    simp [toGetAt?_eq_toSequence_getAt?] at lm3
    refine Sequence.getAt?_eq_none_and_sub_one_isSome_iff_length_eq lm1 _ |>.mp (And.intro ?_ ?_)
    · have lm4 := getAt?_length_eq_none req
      refine (lm3 _).trans (Eq.trans ?_  lm4)
      congr
      refine Nat.sub_one_add_one ?_
      exact length_ne_zero_of_nonempty_finite lm2 req
    · have lm4 := getAt?_length_sub_one_isSome_iff_nonempty req |>.mpr lm2
      revert lm4
      simp [Option.isSome_iff_exists]
      intro a lm4
      exists a
      refine (lm3 _).trans (Eq.trans ?_  lm4)
      congr
      refine Nat.sub_one_add_one ?_
      intro cont
      rcases lm5: (toSequence seq).length req with _ | len
      · have lm6 := getAt?_length_eq_none req
        simp [lm5] at lm4 lm6
        simp [lm4] at lm6
      · rewrite [lm5] at cont
        dsimp at cont
        subst cont
        rewrite [lm5] at lm4
        dsimp at lm4 lm5
        replace lm5 := length?_eq_natCast_iff_length_eq.mpr (Exists.intro _ lm5)
        have lm6 := tb.tailBy_empty_of_length?_eq_one lm5
        simp [lm6] at lm1


end TailOp

section ConsOpTailOp

variable {C: Type _} {α: Type _} [SequenceLike C α]
         {cb: ConsOp C α} {tb: TailOp C α} {a: α} {seq: C}

namespace ConsOp

theorem consBy_tailBy : tb.tailBy (cb.consBy a seq) = seq := by
  refine toSequenceAt_getAt?_ext ?_
  refine funext ?_
  intro n
  have lm1 := cb.consBy_tail_at a seq
  have lm2 := tb.tailBy_cons_at (cb.consBy a seq)
  dsimp only [toGetAt?_eq_toSequence_getAt?] at lm1 lm2
  specialize lm1 n
  specialize lm2 n
  exact lm2.trans lm1

end ConsOp

namespace TailOp

theorem tailBy_consBy (req: (seq : Sequence α).toEmptyLabel = .nonempty)
  : cb.consBy ((seq : Sequence α).head req) (tb.tailBy seq) = seq := by
  have lm1 := req
  revert req
  simp [toEmptyLabel_eq_nonempty_iff_getAt?_0_eq_some]
  intro a lm2
  refine toSequenceAt_getAt?_ext ?_
  refine funext ?_
  intro n
  have lm3 := tb.tailBy_cons_at seq
  have lm4 := cb.consBy_tail_at a (tb.tailBy seq)
  have lm5 := cb.consBy_head_at a (tb.tailBy seq)
  dsimp only [toGetAt?_eq_toSequence_getAt?] at lm3 lm4 lm5
  induction n with
  | zero =>
    simp only [lm2]
    refine Eq.trans ?_ lm5
    congr
    refine Option.some_inj.mp ?_
    rw [← lm2, ← head?_eq_some_head, head?_eq_getAt?_zero]
  | succ n lm6 =>
    have lm7 := head?_eq_getAt?_zero.trans lm2
    rewrite [head?_eq_some_head lm1, Option.some_inj] at lm7
    simp only [lm7] at lm6 ⊢
    specialize lm3 n
    specialize lm4 n
    calc
      _ = _ := lm4
      _ = _ := lm3


end TailOp

end ConsOpTailOp


structure NilOp (C: Type _) (α: Type _) [SequenceLike C α] where
  nilBy: C
  nilBy_empty : (toSequence nilBy).toEmptyLabel = .empty

/-
structure AppendOp (C: Type _) (α: Type _) [SequenceLike C α] where
  appendBy: C → C → C
  appendBy_cons
-/

end Nemonuri.SequenceLike

end
