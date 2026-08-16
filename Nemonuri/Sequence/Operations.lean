module

public import Nemonuri.Sequence.Basic

@[expose] public section


namespace Nemonuri.Sequence

variable {α: Type _} {a: α} {seq: Sequence α} {i: ℕ}

--attribute [local ext] Sequence.ext

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

@[defeq]
theorem cons_getAt?_zero : (cons a seq).getAt? 0 = .some a := rfl

@[defeq]
theorem cons_getAt?_add_one_eq_getAt? : (cons a seq).getAt? (i + 1) = seq.getAt? i := rfl

@[defeq]
theorem cons_length?_eq_length?_add_one : (cons a seq).length? = seq.length? + 1 := rfl

theorem cons_head? : (cons a seq).head? = .some a :=
  calc
    _ = _ := head?_eq_getAt?_zero
    _ = _ := cons_getAt?_zero

theorem cons_nonempty : (cons a seq).toEmptyLabel = .nonempty := by
  rw [toEmptyLabel_eq_nonempty_iff_exists_getAt?_eq_some]
  have lm1 := @seq.cons_getAt?_zero _ a
  exists 0
  exists a

theorem cons_head : (cons a seq).head cons_nonempty = a := by
  rw [← Option.some_inj]
  rw [← head?_eq_some_head]
  exact cons_head?

theorem cons_toFinLabel_eq_toFinLabel : (cons a seq).toFinLabel = seq.toFinLabel := by
  cases lm1: seq.toFinLabel
  · rewrite [toFinLabel_eq_finite_iff_length?_eq_natCast] at lm1 ⊢
    have lm2 := @seq.cons_length?_eq_length?_add_one _ a
    rcases lm1 with ⟨n, lm1⟩
    exists (n+1)
    rw [Nat.cast_add, ← lm1, Nat.cast_one]
    exact lm2
  · rewrite [toFinLabel_eq_infinite_iff_length?_eq_top] at lm1 ⊢
    have lm2 := @seq.cons_length?_eq_length?_add_one _ a
    rw [lm1] at lm2
    simpa using lm2





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

@[defeq]
theorem tail_getAt?_eq_getAt?_add_one : seq.tail.getAt? i = seq.getAt? (i+1) := rfl

@[defeq]
theorem tail_length?_eq_length?_sub_one : seq.tail.length? = seq.length? - 1 := rfl

theorem tail_toFinLabel_eq_toFinLabel : seq.tail.toFinLabel = seq.toFinLabel := by
  cases lm1: seq.toFinLabel
  · simp only [toFinLabel_eq_finite_iff_length?_eq_natCast] at lm1
    simp only [toFinLabel_eq_finite_iff_length?_ne_top]
    dsimp [tail_length?_eq_length?_sub_one]
    obtain ⟨n, lm1⟩ := lm1
    rw [lm1]
    simp
  · simp only [toFinLabel_eq_infinite_iff_length?_eq_top] at lm1 ⊢
    dsimp [tail_length?_eq_length?_sub_one]
    rw [lm1]
    simp

theorem tail_length_eq_length_sub_one (req: seq.toFinLabel = .finite)
  : seq.tail.length (seq.tail_toFinLabel_eq_toFinLabel.trans req) = seq.length req - 1 := by
  have lm1 := seq.tail_length?_eq_length?_sub_one
  rw [← ENat.coe_inj]
  conv => rhs; rw [ENat.coe_sub]; rw [← length?_eq_natCast_length]
  conv => lhs; rw [← length?_eq_natCast_length]; rw [lm1]
  rw [Nat.cast_one]

theorem tail_length_lt_length (req1: seq.toFinLabel = .finite) (req2: seq.toEmptyLabel = .nonempty)
  : seq.tail.length (seq.tail_toFinLabel_eq_toFinLabel.trans req1) < seq.length req1 := by
  have lm1 := seq.tail_length_eq_length_sub_one req1
  rw [lm1]
  refine Nat.sub_one_lt ?_
  rewrite [toEmptyLabel_eq_nonempty_iff_length?_ne_zero] at req2
  intro cont
  exact req2 (length?_eq_zero_of_length_eq_zero cont)


theorem cons_eta (req: seq.toEmptyLabel = .nonempty)
  : (cons (seq.head req) seq.tail) = seq := by
  have lm1 := req
  revert lm1
  simp [toEmptyLabel_eq_nonempty_iff_getAt?_0_eq_some]
  intro a lm2
  have lm3 := lm2
  rewrite [← head?_eq_getAt?_zero, head?_eq_some_head req, Option.some_inj] at lm3
  rw [lm3]
  refine Sequence.ext ?_
  refine funext ?_
  intro i
  cases i with
  | zero =>
    calc
      _ = _ := cons_getAt?_zero
      _ = _ := lm2.symm
  | succ i =>
    dsimp [cons_getAt?_add_one_eq_getAt?, tail_getAt?_eq_getAt?_add_one]

theorem cons_tail {a: α} : (cons a seq).tail = seq := by
  refine Sequence.ext ?_
  refine funext ?_
  intro i
  dsimp [tail]
  exact cons_getAt?_add_one_eq_getAt?


def nil : Sequence α where
  getAt? _ := .none
  length? := 0
  length?_getAt? := by
    intro _; simp

@[defeq]
theorem nil_getAt?_none {i: ℕ} : (nil : Sequence α).getAt? i = .none := rfl

@[defeq]
theorem nil_length?_eq_zero : (nil : Sequence α).length? = 0 := rfl

theorem nil_empty : (nil : Sequence α).toEmptyLabel = .empty := by
  have lm1 := @nil_length?_eq_zero α
  exact toEmptyLabel_eq_empty_iff_length?_eq_zero.mpr lm1

theorem eq_nil_iff_empty : (seq = nil) ↔ (seq.toEmptyLabel = .empty) := by
  constructor
  · intro lm1; subst lm1; exact nil_empty
  · intro lm1
    rw [Sequence.ext_iff, funext_iff]
    dsimp [nil_getAt?_none]
    rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm1
    exact lm1


theorem nil_tail_eq_nil : (nil : Sequence α).tail = nil := by
  refine Sequence.ext ?_
  dsimp only [nil, tail]


theorem empty_of_tail_eq_self (req1: seq.toFinLabel = .finite) (req2: seq.tail = seq)
  : seq.toEmptyLabel = .empty := by
  rewrite [Sequence.ext_iff, funext_iff] at req2
  simp only [tail_getAt?_eq_getAt?_add_one] at req2
  have lm1 := seq.getAt?_length_eq_none req1
  cases lm2: seq.toEmptyLabel
  · rfl
  · have lm3 := length_pos_of_nonempty_finite lm2 req1
    have lm4 := seq.getAt?_length_sub_one_isSome_iff_nonempty req1 |>.mpr lm2
    specialize req2 (seq.length req1 - 1)
    conv at req2 =>
      lhs
      arg 2
      rw [Nat.sub_one_add_one_eq_of_pos lm3]
    rewrite [Option.isSome_iff_exists] at lm4
    rcases lm4 with ⟨a, lm4⟩
    rewrite [lm1, lm4] at req2
    simp at req2

theorem tail_eq_self_iff_empty (req: seq.toFinLabel = .finite)
  : (seq.tail = seq) ↔ (seq.toEmptyLabel = .empty) := by
  constructor
  · intro lm1
    exact seq.empty_of_tail_eq_self req lm1
  · intro lm1
    refine Sequence.ext ?_
    refine funext ?_
    intro i
    rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm1
    dsimp [tail_getAt?_eq_getAt?_add_one]
    have lm2 := lm1 (i+1)
    have lm3 := lm1 i
    calc
      _ = _ := lm2
      _ = _ := lm3.symm

theorem tail_eq_self_iff_eq_nil (req: seq.toFinLabel = .finite)
  : (seq.tail = seq) ↔ (seq = nil) :=
  calc
    _ ↔ _ := seq.tail_eq_self_iff_empty req
    _ ↔ _ := seq.eq_nil_iff_empty.symm


theorem cons_ne_nil {a: α} : cons a seq ≠ nil := by
  intro lm1
  have lm2 := congrArg Sequence.toEmptyLabel lm1
  rewrite [cons_nonempty, nil_empty] at lm2
  simp at lm2



theorem tail_cons_eq_self_iff {a: α}
  : ((cons a seq.tail) = seq) ↔ (∃(req: seq.toEmptyLabel = .nonempty), (seq.head req = a)) := by
  constructor
  · intro lm1
    refine Exists.intro ?_ ?_
    · have lm2 := congrArg Sequence.toEmptyLabel lm1
      rewrite [cons_nonempty] at lm2
      exact lm2.symm
    · conv =>
        lhs
        arg 1
        rw [← lm1]
      rw [← Option.some_inj, ← head?_eq_some_head]
      exact cons_head?
  · rintro ⟨lm1, lm2⟩
    rw [← lm2]
    exact cons_eta _




def single (a: α) : Sequence α where
  getAt? i :=
    match i with
    | 0 => .some a
    | i + 1 => .none
  length? := 1
  length?_getAt? := by
    intro i2
    split
    · simp
    · simp

@[defeq]
theorem single_length?_eq_one : (single a).length? = 1 := rfl


def singleCons (a: α) : Sequence α := cons a nil

theorem singleCons_eq_single : @singleCons = @single := by
  ext α a
  refine Sequence.ext ?_
  dsimp [singleCons]
  refine funext ?_
  intro i
  dsimp [single]
  split
  · exact cons_getAt?_zero
  · simp
    rw [cons_getAt?_add_one_eq_getAt?]
    dsimp [nil]


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


theorem takeRec_eq_take_at_zero : @takeRec α 0 = @take α 0 := by
  refine funext ?_
  intro seq
  refine Sequence.ext ?_
  dsimp [takeRec, take, nil]

theorem takeRec_eq_take_at (n: ℕ) : @takeRec α n = @take α n := by
  refine funext ?_
  intro seq
  cases n with
  | zero => rw [takeRec_eq_take_at_zero]
  | succ n =>
    refine Sequence.ext ?_
    unfold takeRec
    dsimp [take]
    refine funext ?_
    intro i
    split <;> split <;> rename_i lm2 lm3
    · rfl
    · rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm2
      exact lm2 i
    · revert lm2; simp only [EmptyLabel.ne_empty_iff_eq_nonempty]; intro lm2
      have lm4 := seq.cons_eta lm2
      rewrite [Sequence.ext_iff] at lm4
      rewrite [funext_iff] at lm4
      specialize lm4 i
      rw [← lm4]
      cases i with
      | zero => dsimp [cons_getAt?_zero]
      | succ i =>
        have lm6 x := @cons_getAt?_add_one_eq_getAt? α (seq.head lm2) x i
        simp [lm6]
        have lm7 := funext_iff.mp (takeRec_eq_take_at n) seq.tail
        rw [lm7];
        dsimp [take]
        split <;> rename_i lm8
        · rfl
        · simp at lm3; contradiction
    · revert lm2; simp only [EmptyLabel.ne_empty_iff_eq_nonempty]; intro lm2
      simp at lm3
      rcases i with _ | i
      · simp at lm3
      · rw [cons_getAt?_add_one_eq_getAt?]
        refine length?_le_iff_getAt?_eq_none.mp ?_
        have lm4 := funext_iff.mp (takeRec_eq_take_at n) seq.tail
        rw [lm4]
        dsimp [take]
        rewrite [← Nat.le_iff_lt_add_one, ← ENat.coe_le_coe] at lm3
        split <;> rename_i lm5
        · refine le_of_lt ?_
          calc
            _ < _ := lm5
            _ ≤ _ := lm3
        · exact lm3


theorem takeRec_eq_take : @takeRec = @take := by
  refine funext ?_
  intro _
  refine funext ?_
  exact takeRec_eq_take_at


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


def appendRec (seq1: Sequence α) (req: seq1.toFinLabel = .finite) (seq2: Sequence α) :=
  if lm1: seq1.toEmptyLabel = .empty then
    seq2
  else
    have lm2 : seq1.toEmptyLabel = .nonempty := EmptyLabel.ne_empty_iff_eq_nonempty.mp lm1
    cons (seq1.head lm2) (appendRec seq1.tail (seq1.tail_toFinLabel_eq_toFinLabel.trans req) seq2)
  termination_by (seq1.length req)
  decreasing_by
    exact seq1.tail_length_lt_length req lm2


theorem appendRec_eq_append_at
  (seq1: Sequence α) (req: seq1.toFinLabel = .finite) (seq2: Sequence α)
  : appendRec seq1 req seq2 = append seq1 req seq2 := by
  refine Sequence.ext ?_
  refine funext ?_
  intro i
  dsimp [append]
  split <;> rename_i lm1
  · unfold appendRec
    split <;> rename_i lm2
    · have lm3 := length_eq_zero_of_empty lm2
      simp [lm3] at lm1
    · dsimp
      revert lm2; simp only [EmptyLabel.ne_empty_iff_eq_nonempty]; intro lm2
      have lm3 := appendRec_eq_append_at seq1.tail (seq1.tail_toFinLabel_eq_toFinLabel.trans req) seq2
      rw [lm3]
      rcases i with _ | i
      · rw [cons_getAt?_zero]
        rw [← head?_eq_some_head]
        exact head?_eq_getAt?_zero
      · rw [cons_getAt?_add_one_eq_getAt?]
        dsimp [append]
        split <;> rename_i lm4
        · exact seq1.tail_getAt?_eq_getAt?_add_one
        · simp at lm4
          rewrite [← Nat.lt_sub_iff_add_lt] at lm1
          have lm5 := seq1.tail_length_eq_length_sub_one req
          rewrite [← lm5] at lm1
          exact Nat.not_le_of_lt lm1 lm4 |> False.elim
  · simp at lm1
    unfold appendRec
    dsimp
    split <;> rename_i lm2
    · have lm3 := length_eq_zero_of_empty lm2
      simp [lm3]
    · revert lm2; simp only [EmptyLabel.ne_empty_iff_eq_nonempty]; intro lm2
      have lm3 := appendRec_eq_append_at seq1.tail (seq1.tail_toFinLabel_eq_toFinLabel.trans req) seq2
      rw [lm3]
      rcases i with _ | i
      · simp at lm1
        replace lm1 := seq1.length?_eq_zero_of_length_eq_zero lm1
        rewrite [← toEmptyLabel_eq_empty_iff_length?_eq_zero] at lm1
        simp [lm1] at lm2
      · rw [cons_getAt?_add_one_eq_getAt?]
        dsimp [append]
        split <;> rename_i lm4
        · have lm5 := seq1.tail_length_eq_length_sub_one req
          rewrite [← Nat.sub_le_iff_le_add, ← lm5] at lm1
          exact Nat.not_le_of_lt lm4 lm1 |> False.elim
        · have lm5 := seq1.tail_length_eq_length_sub_one req
          simp at lm4
          have lm6 := seq1.length_pos_of_nonempty_finite lm2 req
          refine congrArg _ ?_
          omega
  termination_by (seq1.length req)
  decreasing_by
    · exact seq1.tail_length_lt_length req lm2
    · exact seq1.tail_length_lt_length req lm2


theorem appendRec_eq_append : @appendRec = @append := by
  ext
  exact appendRec_eq_append_at _ _ _





end Nemonuri.Sequence


end
