module

public import Nemonuri.Sequence.Labels



@[expose] public section

namespace Nemonuri


structure Sequence (α: Type _) where
  getAt? : ℕ → (Option α)
  length? : ℕ∞
  length?_getAt? {i: ℕ} : (i < length?) ↔ (getAt? i).isSome

namespace Sequence

variable {α: Type _} {seq: Sequence α}

def getAt (seq: Sequence α) (i: ℕ) (req: i < seq.length?) : α := (seq.getAt? i).get (seq.length?_getAt?.mp req)

theorem getAt?_eq_some_getAt {i: ℕ} (req: i < seq.length?)
  : seq.getAt? i = .some (seq.getAt i req) := by
  dsimp [getAt]
  simp only [Option.some_get]

theorem length?_le_iff_getAt?_isNone {i: ℕ} : (seq.length? ≤ i) ↔ (seq.getAt? i).isNone := by
  have lm1 := @seq.length?_getAt? i
  replace lm1 := Iff.not lm1
  simpa using lm1

theorem length?_le_iff_getAt?_eq_none {i: ℕ} : (seq.length? ≤ i) ↔ ((seq.getAt? i) = .none) :=
  calc
    (seq.length? ≤ i) ↔ _ := length?_le_iff_getAt?_isNone
    _ ↔ _ := Option.isNone_iff_eq_none


/- Mathlib - Stream'.IsSeq -/
theorem add_one_getAt?_none_of_getAt?_none {i: ℕ} (req: seq.getAt? i = .none) : seq.getAt? (i + 1) = .none := by
  have lm1 := @seq.length?_le_iff_getAt?_eq_none
  have lm2 := @lm1 i |>.mpr req
  have lm3 := @lm1 (i+1) |>.mp
  refine lm3 ?_
  calc
    _ ≤ _ := lm2
    _ ≤ _ := by simp


instance : GetElem? (Sequence α) ℕ α (fun seq i => i < seq.length?) where
  getElem seq i h := seq.getAt i h
  getElem? seq i := seq.getAt? i

instance : LawfulGetElem (Sequence α) ℕ α (fun seq i => i < seq.length?) where
  getElem?_def seq i := by
    simp [length?_getAt?]
    split <;> rename_i lm1
    · rw [Option.eq_some_iff_get_eq]
      refine Exists.intro ?_ ?_
      · exact lm1
      · rfl
    · simp at lm1
      exact lm1

@[defeq]
theorem getAt?_eq_getElem? {n: ℕ} : seq.getAt? n = seq[n]? := rfl

@[defeq]
theorem getAt_eq_getElem {n: ℕ} (req: n < seq.length?) : seq.getAt n req = seq[n]'(req) := rfl


def toEmptyLabel (seq: Sequence α) : EmptyLabel := .ofENat seq.length?

theorem toEmptyLabel_eq_empty_iff_length?_eq_zero
  : (seq.toEmptyLabel = .empty) ↔ (seq.length? = 0) := by
  dsimp [toEmptyLabel]
  exact EmptyLabel.ofENat_empty_iff_eq_zero

theorem toEmptyLabel_eq_nonempty_iff_length?_ne_zero
  : (seq.toEmptyLabel = .nonempty) ↔ (seq.length? ≠ 0) := by
  have lm1 := seq.toEmptyLabel_eq_empty_iff_length?_eq_zero
  cases lm2: seq.toEmptyLabel
  · simp; exact lm1.mp lm2
  · simp; simpa [lm2] using lm1

theorem toEmptyLabel_eq_nonempty_iff_length?_pos
  : (seq.toEmptyLabel = .nonempty) ↔ (0 < seq.length?) := by
  dsimp [toEmptyLabel]
  exact EmptyLabel.ofENat_nonempty_iff_pos

theorem toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none
  : (seq.toEmptyLabel = .empty) ↔ (∀n, seq.getAt? n = .none) := by
  have lm2 := @seq.length?_le_iff_getAt?_eq_none
  rw [toEmptyLabel_eq_empty_iff_length?_eq_zero]
  constructor
  · intro lm1
    rw [lm1] at lm2
    simp at lm2; exact @lm2
  · intro lm1
    replace lm2 := forall_congr' @lm2
    replace lm2 := lm2.mpr lm1
    cases lm3: seq.length? <;> simp [lm3] at lm2
    rename_i n
    specialize lm2 0
    simp at lm2 ⊢
    exact lm2

theorem toEmptyLabel_eq_nonempty_iff_exists_getAt?_eq_some
  : (seq.toEmptyLabel = .nonempty) ↔ (∃n a, seq.getAt? n = .some a) := by
  have lm1 := seq.toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none
  cases lm2: seq.toEmptyLabel
  · replace lm1 := lm1.mp lm2
    simp [← Option.eq_none_iff_forall_ne_some]
    exact lm1
  · simp [lm2, Option.ne_none_iff_exists'] at lm1
    simpa using lm1


theorem toEmptyLabel_eq_nonempty_iff_getAt?_0_eq_some
  : (seq.toEmptyLabel = .nonempty) ↔ (∃a, seq.getAt? 0 = .some a) := by
  by_cases lm2: seq.getAt? 0 = .none
  · have lm3 (n: ℕ) : seq.getAt? n = .none := Nat.rec lm2 (@seq.add_one_getAt?_none_of_getAt?_none) n
    have lm4 := seq.toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none.mpr lm3
    simp [lm4, ← Option.eq_none_iff_forall_ne_some]
    exact lm2
  · simp [Option.ne_none_iff_exists'] at lm2
    simp [lm2]
    obtain ⟨a, lm2⟩ := lm2
    by_contra cont
    simp [EmptyLabel.ne_nonempty_iff_eq_empty, toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at cont
    specialize cont 0
    simp [cont] at lm2




def toFinLabel (seq: Sequence α) : FiniteLabel := .ofENat seq.length?

theorem toFinLabel_eq_finite_iff_length?_eq_natCast
  : (seq.toFinLabel = .finite) ↔ ∃n, (seq.length? = Nat.cast n) := by
  dsimp [toFinLabel]
  exact FiniteLabel.ofENat_finite_iff_eq_natCast

theorem toFinLabel_eq_finite_iff_length?_lt_top
  : (seq.toFinLabel = .finite) ↔ (seq.length? < ⊤) := by
  dsimp [toFinLabel]
  exact FiniteLabel.ofENat_finite_iff_lt_top

theorem toFinLabel_eq_finite_iff_length?_ne_top
  : (seq.toFinLabel = .finite) ↔ (seq.length? ≠ ⊤) := by
  dsimp [toFinLabel]
  exact FiniteLabel.ofENat_finite_iff_ne_top

theorem toFinLabel_eq_infinite_iff_length?_eq_top
  : (seq.toFinLabel = .infinite) ↔ (seq.length? = ⊤) := by
  dsimp [toFinLabel]
  exact FiniteLabel.ofENat_infinite_iff_eq_top

theorem toFinLabel_eq_infinite_iff_forall_getAt?_eq_some
  : (seq.toFinLabel = .infinite) ↔ (∀n, ∃a, seq.getAt? n = .some a) := by
  have lm1 := @seq.length?_getAt?
  constructor
  · intro lm2
    rw [toFinLabel_eq_infinite_iff_length?_eq_top] at lm2
    simp [lm2, Option.isSome_iff_exists] at lm1
    exact @lm1
  · intro lm2
    simp [← Option.isSome_iff_exists] at lm2
    replace lm2 := forall_congr' @lm1 |>.mpr lm2
    simp [← ENat.eq_top_iff_forall_gt] at lm2
    exact toFinLabel_eq_infinite_iff_length?_eq_top.mpr lm2

theorem toFinLabel_eq_finite_iff_exists_getAt?_eq_none
  : (seq.toFinLabel = .finite) ↔ (∃n, seq.getAt? n = .none) := by
  have lm1 := seq.toFinLabel_eq_infinite_iff_forall_getAt?_eq_some
  cases lm2: seq.toFinLabel
  · simp [lm2] at lm1
    obtain ⟨n, lm1⟩ := lm1
    conv at lm1 => arg 2; arg 1; rw [Eq.comm]
    simp [← Option.eq_none_iff_forall_some_ne] at lm1
    simp
    exists n
  · simp [lm2] at lm1
    simp
    intro n
    simp [Option.ne_none_iff_exists']
    exact lm1 n


theorem not_empty_infinite (req1: seq.toEmptyLabel = .empty) (req2: seq.toFinLabel = .infinite) : False := by
  rewrite [toEmptyLabel_eq_empty_iff_length?_eq_zero] at req1
  rewrite [toFinLabel_eq_infinite_iff_length?_eq_top] at req2
  simp [req2] at req1

theorem nonempty_of_infinite (req: seq.toFinLabel = .infinite) : seq.toEmptyLabel = .nonempty := by
  have lm1 := fun h1 => seq.not_empty_infinite h1 req
  cases lm2: seq.toEmptyLabel
  · exact False.elim (lm1 lm2)
  · rfl





def head (seq: Sequence α) (req: seq.toEmptyLabel = .nonempty) : α :=
  seq[0]'(seq.toEmptyLabel_eq_nonempty_iff_length?_pos.mp req)

@[defeq]
theorem head_eq_getElem (req: seq.toEmptyLabel = .nonempty)
  : seq.head req = seq[0]'(seq.toEmptyLabel_eq_nonempty_iff_length?_pos.mp req) :=
  rfl

def head? (seq: Sequence α) : Option α :=
  match lm1: seq.toEmptyLabel with
  | .nonempty => .some (seq.head lm1)
  | .empty => .none

theorem head?_eq_some_head (req: seq.toEmptyLabel = .nonempty) : seq.head? = .some (seq.head req) := by
  dsimp [head?]
  split <;> rename_i heq
  · rfl
  · simp [heq] at req

theorem head?_eq_getElem? : seq.head? = seq[0]? := by
  dsimp [← getAt?_eq_getElem?]
  dsimp [head?]
  split <;> rename_i heq
  · dsimp [head, ← getAt_eq_getElem]
    symm
    refine seq.getAt?_eq_some_getAt ?_
  · simp [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at heq
    symm
    exact heq 0




def length (seq: Sequence α) (req: seq.toFinLabel = .finite) : ℕ :=
  seq.length?.lift (seq.toFinLabel_eq_finite_iff_length?_lt_top.mp req)


theorem length?_eq_natCast_length (req: seq.toFinLabel = .finite) : seq.length? = Nat.cast (seq.length req) := by
  dsimp [length]
  simp only [ENat.coe_lift]

@[defeq]
theorem length_eq_length?_lift (req: seq.toFinLabel = .finite)
  : seq.length req = seq.length?.lift (toFinLabel_eq_finite_iff_length?_lt_top.mp req) := by
  rfl

def last (seq: Sequence α) (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite) :=
  seq[(seq.length req2) - 1]'(by
    have lm1 := seq.length?_eq_natCast_length req2
    rw [lm1]
    rw [ENat.coe_lt_coe]
    rewrite [toEmptyLabel_eq_nonempty_iff_length?_pos, lm1] at req1
    conv at req1 => lhs; change (Nat.cast 0)
    rw [ENat.coe_lt_coe] at req1
    refine Nat.sub_one_lt ?_
    exact Nat.ne_zero_of_lt req1 )

def last? (seq: Sequence α) : Option α :=
  match lm1: seq.toEmptyLabel, lm2: seq.toFinLabel with
  | .nonempty, .finite => .some (seq.last lm1 lm2)
  | _, _ => .none

theorem last?_eq_some_last (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite)
  : seq.last? = .some (seq.last req1 req2) := by
  dsimp [last?]
  split
  · rfl
  · rename_i lm1
    exact False.elim (lm1 req1 req2)

section Ext

variable {seq2: Sequence α}

theorem length?_eq_of_infinites
  (req1: seq.toFinLabel = .infinite) (req2: seq2.toFinLabel = .infinite)
  : seq.length? = seq2.length? := by
  rewrite [toFinLabel_eq_infinite_iff_length?_eq_top] at req1 req2
  rw [req1, req2]

theorem length?_ne_of_toFinLabel_ne (req: seq.toFinLabel ≠ seq2.toFinLabel)
  : seq.length? ≠ seq2.length? := by
  cases lm1: seq2.toFinLabel
  · simp [lm1, FiniteLabel.ne_finite_iff_eq_infinite] at req
    rewrite [toFinLabel_eq_finite_iff_length?_ne_top] at lm1
    rewrite [toFinLabel_eq_infinite_iff_length?_eq_top] at req
    rw [req]; symm; exact lm1
  · simp [lm1, FiniteLabel.ne_infinite_iff_eq_finite] at req
    rewrite [toFinLabel_eq_finite_iff_length?_ne_top] at req
    rewrite [toFinLabel_eq_infinite_iff_length?_eq_top] at lm1
    rw [lm1]; exact req

theorem length?_eq_of_getAt?_eq_of_finites
  (req1: seq.getAt? = seq2.getAt?) (req2: seq.toFinLabel = .finite) (req3: seq2.toFinLabel = .finite)
  : seq.length? = seq2.length? := by
  rewrite [funext_iff] at req1
  simp [toFinLabel_eq_finite_iff_length?_eq_natCast] at req2 req3
  obtain ⟨len1, lm1⟩ := req2
  obtain ⟨len2, lm2⟩ := req3
  have lm1_1 := @seq.length?_le_iff_getAt?_eq_none
  have lm2_1 := @seq2.length?_le_iff_getAt?_eq_none
  simp [lm1] at lm1_1
  simp [lm2] at lm2_1
  have lm1_len1 := @lm1_1 len1
  have lm1_len2 := @lm1_1 len2
  have lm2_len1 := @lm2_1 len1
  have lm2_len2 := @lm2_1 len2
  have req_len1 := req1 len1
  have req_len2 := req1 len2
  simp at lm1_len1 lm1_len2 lm2_len1 lm2_len2
  rewrite [req_len2, lm2_len2] at lm1_len2
  rewrite [← req_len1, lm1_len1] at lm2_len1
  simp at lm1_len2 lm2_len1
  have lm3 := Nat.eq_iff_le_and_ge.mpr (.intro lm1_len2 lm2_len1)
  simp [lm1, lm2, lm3]

theorem toFinLabel_eq_of_getAt?_eq (req: seq.getAt? = seq2.getAt?) : seq.toFinLabel = seq2.toFinLabel := by
  rewrite [funext_iff] at req
  cases lm1: seq2.toFinLabel
  · rewrite [seq2.toFinLabel_eq_finite_iff_exists_getAt?_eq_none] at lm1
    obtain ⟨n, lm1⟩ := lm1
    specialize req n
    rewrite [lm1] at req
    refine seq.toFinLabel_eq_finite_iff_exists_getAt?_eq_none.mpr ?_
    exists n
  · rewrite [seq2.toFinLabel_eq_infinite_iff_forall_getAt?_eq_some] at lm1
    refine seq.toFinLabel_eq_infinite_iff_forall_getAt?_eq_some.mpr ?_
    intro n
    specialize req n
    obtain ⟨a1, lm1⟩ := lm1 n
    rewrite [← req] at lm1
    exists a1


theorem length?_eq_of_getAt?_eq (req: seq.getAt? = seq2.getAt?) : seq.length? = seq2.length? := by
  by_cases lm1: seq.toFinLabel = seq2.toFinLabel
  · cases lm2: seq2.toFinLabel
    · rewrite [lm2] at lm1
      exact seq.length?_eq_of_getAt?_eq_of_finites req lm1 lm2
    · rewrite [lm2] at lm1
      exact seq.length?_eq_of_infinites lm1 lm2
  · have lm2 := toFinLabel_eq_of_getAt?_eq req
    exact absurd lm2 lm1


theorem ext (req: seq.getAt? = seq2.getAt?) : seq = seq2 := by
  have lm3 := length?_eq_of_getAt?_eq req
  rcases seq with ⟨seq_g, seq_l, lm1⟩
  rcases seq2 with ⟨seq2_g, seq2_l, lm2⟩
  simp at lm3
  congr



theorem ext_iff : (seq.getAt? = seq2.getAt?) ↔ (seq = seq2) := ⟨Sequence.ext, congrArg (Sequence.getAt?)⟩

end Ext

end Sequence

end Nemonuri

end
