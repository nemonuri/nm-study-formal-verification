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

theorem add_getAt?_none_of_getAt?_none {i: ℕ} (req: seq.getAt? i = .none) {i2: ℕ} : seq.getAt? (i + i2) = .none := by
  induction i2 with
  | zero => dsimp; exact req
  | succ i2 lm1 =>
    rw [← Nat.add_assoc]
    refine seq.add_one_getAt?_none_of_getAt?_none ?_
    exact lm1


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

theorem toEmptyLabel_eq_empty_iff_getAt?_0_eq_none
  : (seq.toEmptyLabel = .empty) ↔ (seq.getAt? 0 = .none) := by
  constructor
  · intro lm1
    rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm1
    exact lm1 0
  · intro lm1
    have lm2 n := @seq.add_one_getAt?_none_of_getAt?_none _ n
    refine seq.toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none.mpr ?_
    intro n
    exact Nat.recAux lm1 lm2 n




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


theorem empty_and_infinite_iff_false
  : ((seq.toEmptyLabel = .empty) ∧ (seq.toFinLabel = .infinite)) ↔ False := by
  constructor
  · rintro ⟨lm1, lm2⟩
    rewrite [toEmptyLabel_eq_empty_iff_length?_eq_zero] at lm1
    rewrite [toFinLabel_eq_infinite_iff_length?_eq_top] at lm2
    simp [lm2] at lm1
  · intro lm1
    exact False.elim lm1

theorem nonempty_of_infinite (req: seq.toFinLabel = .infinite) : seq.toEmptyLabel = .nonempty := by
  have lm1 := fun h1 => seq.empty_and_infinite_iff_false.mp (And.intro h1 req)
  cases lm2: seq.toEmptyLabel
  · exact False.elim (lm1 lm2)
  · rfl

theorem finite_of_empty (req: seq.toEmptyLabel = .empty) : seq.toFinLabel = .finite := by
  have lm1 := fun h1 => seq.empty_and_infinite_iff_false.mp (And.intro req h1)
  simp [FiniteLabel.ne_infinite_iff_eq_finite] at lm1
  exact lm1

theorem finite_of_length?_eq_natCast {n: ℕ} (req: seq.length? = (Nat.cast n)) : seq.toFinLabel = .finite := by
  refine toFinLabel_eq_finite_iff_length?_eq_natCast.mpr ?_
  exists n


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

theorem head?_eq_getAt?_zero : seq.head? = seq.getAt? 0 := by
  rw [head?_eq_getElem?]
  dsimp [GetElem?.getElem?]




def length (seq: Sequence α) (req: seq.toFinLabel = .finite) : ℕ :=
  seq.length?.lift (seq.toFinLabel_eq_finite_iff_length?_lt_top.mp req)


theorem length?_eq_natCast_length (req: seq.toFinLabel = .finite) : seq.length? = Nat.cast (seq.length req) := by
  dsimp [length]
  simp only [ENat.coe_lift]

@[defeq]
theorem length_eq_length?_lift (req: seq.toFinLabel = .finite)
  : seq.length req = seq.length?.lift (toFinLabel_eq_finite_iff_length?_lt_top.mp req) :=
  rfl

theorem length?_eq_natCast_iff_length_eq {n: ℕ}
  : (seq.length? = (Nat.cast n)) ↔ (∃req, (seq.length req) = n) := by
  constructor
  · intro lm1
    refine Exists.intro ?_ ?_
    · rw [toFinLabel_eq_finite_iff_length?_eq_natCast]
      exists n
    · refine ENat.coe_inj.mp ?_
      calc
        _ = _ := (seq.length?_eq_natCast_length _).symm
        _ = _ := lm1
  · rintro ⟨lm1, lm2⟩
    rewrite [← ENat.coe_inj] at lm2
    calc
      _ = _ := seq.length?_eq_natCast_length lm1
      _ = _ := lm2

theorem length?_eq_natCast_iff_length_eq_at (n: ℕ) : (seq.length? = (Nat.cast n)) ↔ (∃req, (seq.length req) = n) :=
  @seq.length?_eq_natCast_iff_length_eq _ n


theorem finite_of_length?_lt_natCast {n: ℕ} (req: seq.length? < (Nat.cast n)) : seq.toFinLabel = .finite := by
  induction n with
  | zero =>
    simp at req
  | succ n lm1 =>
    by_cases lm2: seq.length? = (Nat.cast n)
    · rewrite [length?_eq_natCast_iff_length_eq] at lm2
      rcases lm2 with ⟨lm2, _⟩
      exact lm2
    · have lm3 : Std.IsPartialOrder ℕ∞ := inferInstance
      replace lm3 := lm3.le_antisymm seq.length? (Nat.cast n)
      replace lm3 := fun (And.intro h1 h2) => lm3 h1 h2
      replace lm3 := imp_iff_not lm2 |>.mp lm3
      simp at lm3
      refine lm3 ?_ |> lm1
      have lm4 := ENat.le_sub_one_of_lt req
      conv at lm4 =>
        rhs
        conv => arg 2; rw [← ENat.coe_one]
        rw [← ENat.coe_sub]
        simp
      exact lm4

theorem finite_of_length?_le_natCast {n: ℕ} (req: seq.length? ≤ (Nat.cast n)) : seq.toFinLabel = .finite := by
  by_cases lm1: seq.length? = Nat.cast n
  · exact finite_of_length?_eq_natCast lm1
  · have lm2 : Std.IsPartialOrder ℕ∞ := inferInstance
    replace lm2 := lm2.le_antisymm seq.length? (Nat.cast n)
    replace lm2 := fun (And.intro h1 h2) => lm2 h1 h2
    replace lm2 := imp_iff_not lm1 |>.mp lm2
    simp at lm2
    specialize lm2 req
    exact finite_of_length?_lt_natCast lm2



theorem length_eq_zero_of_length?_eq_zero (req: seq.length? = 0)
  : (seq.length (seq.toEmptyLabel_eq_empty_iff_length?_eq_zero.mpr req |> finite_of_empty) = 0) := by
  have lm1 := seq.toEmptyLabel_eq_empty_iff_length?_eq_zero.mpr req
  have lm2 := finite_of_empty lm1
  have lm3 := length?_eq_natCast_length lm2
  rewrite [lm3, ← ENat.coe_zero] at req
  exact ENat.coe_inj.mp req

theorem length?_eq_zero_of_length_eq_zero {req1: seq.toFinLabel = .finite} (req2: seq.length req1 = 0)
  : seq.length? = 0 := by
  have lm1 := length?_eq_natCast_length req1
  rewrite [← ENat.coe_inj, ← lm1, ENat.coe_zero] at req2
  exact req2




theorem length_le_iff_getAt?_eq_none (req: seq.toFinLabel = .finite) {i: ℕ}
  : ((seq.length req) ≤ i) ↔ ((seq.getAt? i) = .none) := by
  have lm1 := @seq.length?_le_iff_getAt?_eq_none _ i
  have lm2 := seq.length?_eq_natCast_length req
  rewrite [lm2] at lm1
  refine Iff.trans ?_ lm1
  exact ENat.coe_le_coe |> Iff.symm

theorem length_le_iff_getAt?_eq_none_at (req: seq.toFinLabel = .finite) (i: ℕ)
  : ((seq.length req) ≤ i) ↔ ((seq.getAt? i) = .none) :=
  @seq.length_le_iff_getAt?_eq_none _ req i

theorem lt_length_iff_getAt?_isSome (req: seq.toFinLabel = .finite) {i: ℕ}
  : (i < (seq.length req)) ↔ ((seq.getAt? i).isSome) := by
  have lm1 := Iff.not (@seq.length_le_iff_getAt?_eq_none _ req i)
  simp [Option.ne_none_iff_isSome] at lm1
  exact lm1

theorem lt_length_iff_getAt?_isSome_at (req: seq.toFinLabel = .finite) (i: ℕ)
  : (i < (seq.length req)) ↔ ((seq.getAt? i).isSome) :=
  @seq.lt_length_iff_getAt?_isSome _ req i


theorem getAt?_length_eq_none (req: seq.toFinLabel = .finite) : seq.getAt? (seq.length req) = .none := by
  have lm1 := @seq.length_le_iff_getAt?_eq_none _ req (seq.length req)
  simp only [Nat.le_refl] at lm1
  refine lm1.mp ?_
  exact True.intro

theorem getAt?_length_sub_one_isSome_iff_nonempty (req: seq.toFinLabel = .finite)
  : (seq.getAt? (seq.length req - 1)).isSome ↔ (seq.toEmptyLabel = .nonempty) := by
  have lm1 := @seq.lt_length_iff_getAt?_isSome _ req (seq.length req - 1)
  rcases lm2: seq.length req with _ | n
  · simp [lm2] at lm1
    simp [lm1]
    simp only [EmptyLabel.ne_nonempty_iff_eq_empty, toEmptyLabel_eq_empty_iff_length?_eq_zero]
    rw [← ENat.coe_zero, length?_eq_natCast_length req, ENat.coe_inj]
    exact lm2
  · simp [lm2] at lm1
    simp [lm1]
    simp [toEmptyLabel_eq_nonempty_iff_exists_getAt?_eq_some]
    exists n
    simpa [Option.isSome_iff_exists] using lm1

theorem getAt?_length_sub_one_eq_none_iff_empty (req: seq.toFinLabel = .finite)
  : (seq.getAt? (seq.length req - 1) = .none) ↔ (seq.toEmptyLabel = .empty) := by
  refine Decidable.not_iff_not.mp ?_
  simp only [Option.ne_none_iff_isSome, EmptyLabel.ne_empty_iff_eq_nonempty]
  exact getAt?_length_sub_one_isSome_iff_nonempty req

theorem getAt?_length_sub_add_one_eq_none_iff_empty (req: seq.toFinLabel = .finite) {n: ℕ}
  : (seq.getAt? (seq.length req - (n + 1)) = .none) ↔ (seq.toEmptyLabel = .empty) := by
  constructor
  · intro lm1
    have lm2 := @seq.getAt?_length_sub_one_eq_none_iff_empty _ req
    induction n with
    | zero =>
      dsimp at lm1
      exact lm2.mp lm1
    | succ n lm3 =>
      have lm5 := seq.length_le_iff_getAt?_eq_none_at req (seq.length req - (n + 1 + 1))
      replace lm5 := lm5.mpr lm1
      rewrite [← Nat.sub_eq_zero_iff_le] at lm5
      rewrite [Nat.sub_sub_eq_min] at lm5
      dsimp [Min.min] at lm5
      split at lm5
      · rw [toEmptyLabel_eq_empty_iff_length?_eq_zero]
        exact lm5 |> Sequence.length?_eq_zero_of_length_eq_zero
      · simp at lm5
  · intro lm1
    rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm1
    exact lm1 _

theorem getAt?_length_sub_pos_eq_none_iff_empty (req1: seq.toFinLabel = .finite) {n: ℕ} (req2: 0 < n)
  : (seq.getAt? (seq.length req1 - n) = .none) ↔ (seq.toEmptyLabel = .empty) := by
  rcases n with _ | n
  · simp at req2
  · exact seq.getAt?_length_sub_add_one_eq_none_iff_empty req1



theorem length_eq_zero_of_empty (req: seq.toEmptyLabel = .empty) : (seq.length (finite_of_empty req)) = 0 := by
  have lm2 := seq.toEmptyLabel_eq_empty_iff_length?_eq_zero.mp req
  exact length_eq_zero_of_length?_eq_zero lm2

theorem length_ne_zero_of_nonempty_finite (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite)
  : seq.length req2 ≠ 0 := by
  rewrite [toEmptyLabel_eq_nonempty_iff_length?_ne_zero] at req1
  exact fun x => req1 (length?_eq_zero_of_length_eq_zero x)

theorem length_pos_of_nonempty_finite (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite)
  : 0 < seq.length req2 :=
  Nat.pos_of_ne_zero (length_ne_zero_of_nonempty_finite req1 req2)


theorem length_eq_of_getAt?_isSome_and_add_one_eq_none
  (req1: seq.toFinLabel = .finite) {i: ℕ} (req2: (seq.getAt? i).isSome) (req3: seq.getAt? (i + 1) = .none)
  : seq.length req1 = (i + 1) := by
  refine Nat.eq_iff_le_and_ge.mpr (And.intro ?_ ?_)
  · have lm1 := @length_le_iff_getAt?_eq_none _ _ req1 (i + 1)
    exact lm1.mpr req3
  · rw [← Nat.lt_iff_add_one_le]
    have lm1 := @seq.length?_getAt? i
    simp [req2] at lm1
    rewrite [length?_eq_natCast_length req1, ENat.coe_lt_coe] at lm1
    exact lm1


theorem getAt?_eq_none_and_sub_one_isSome_iff_length_eq
  (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite) {i: ℕ}
  : ((seq.getAt? i) = .none ∧ (seq.getAt? (i - 1)).isSome) ↔ (seq.length req2 = i) := by
  constructor
  · rintro ⟨lm3, lm4⟩
    rcases i with _ | i
    · simp [lm3] at lm4
    · simp at lm4
      exact @seq.length_eq_of_getAt?_isSome_and_add_one_eq_none _ req2 i lm4 lm3
  · intro lm3
    have lm1 := getAt?_length_eq_none req2
    have lm2 := getAt?_length_sub_one_isSome_iff_nonempty req2
    simp [req1] at lm2
    simp [← lm3]
    exact And.intro lm1 lm2

def getFromEndAt? (seq: Sequence α) (n: ℕ) (sentinel?: Option α) : Option α :=
  match lm1: seq.toFinLabel with
  | .infinite => .none
  | .finite =>
  match n with
  | 0 => sentinel?
  | n + 1 =>
  if (n + 1) ≤ seq.length lm1 then
    seq.getAt? (seq.length lm1 - (n + 1))
  else
    .none

def getFromLastAt? (seq: Sequence α) (n: ℕ) : Option α := seq.getFromEndAt? (n+1) .none


theorem add_one_getFromLastAt?_none_of_getFromLastAt?_none {n: ℕ} (req: seq.getFromLastAt? n = .none)
  : seq.getFromLastAt? (n+1) = .none := by
  revert req
  dsimp [getFromLastAt?, getFromEndAt?]
  split <;> rename_i lm1
  · simp
  · split <;> rename_i lm2
    · intro lm3
      split <;> rename_i lm4
      · have lm5 := seq.getAt?_length_sub_add_one_eq_none_iff_empty lm1 |>.mp lm3
        rewrite [toEmptyLabel_eq_empty_iff_forall_getAt?_eq_none] at lm5
        exact lm5 _
      · rfl
    · intro lm3; clear lm3
      split <;> rename_i lm3
      · simp at lm2
        have lm4 := Nat.le_trans lm3 lm2
        simp at lm4
      · rfl

theorem add_getFromLastAt?_none_of_getFromLastAt?_none {n: ℕ} (req: seq.getFromLastAt? n = .none) {n2: ℕ}
  : seq.getFromLastAt? (n + n2) = .none := by
  induction n2 with
  | zero =>
    dsimp
    exact req
  | succ n2 lm1 =>
    rewrite [← Nat.add_assoc]
    exact seq.add_one_getFromLastAt?_none_of_getFromLastAt?_none lm1


theorem getFromLastAt?_eq_none_of_infinite (req: seq.toFinLabel = .infinite) {i: ℕ} : seq.getFromLastAt? i = .none := by
  dsimp [getFromLastAt?, getFromEndAt?]
  split <;> rename_i lm1
  · rfl
  · simp [lm1] at req


theorem getFromLastAt?_eq_none_of_empty (req: seq.toEmptyLabel = .empty) {i: ℕ} : seq.getFromLastAt? i = .none := by
  dsimp [getFromLastAt?, getFromEndAt?]
  split <;> rename_i lm1
  · have lm2 := finite_of_empty req
    simp [lm1] at lm2
  · split <;> rename_i lm2
    · have lm3 := seq.toEmptyLabel_eq_empty_iff_length?_eq_zero.mp req
      have lm4 := seq.length_eq_zero_of_length?_eq_zero lm3
      rewrite [lm4] at lm2
      simp at lm2
    · rfl /- no contradiction -/

theorem forall_getFromLastAt?_eq_none_iff_infinite_or_empty
  : (∀(i: ℕ), seq.getFromLastAt? i = .none) ↔ ((seq.toFinLabel = .infinite) ∨ (seq.toEmptyLabel = .empty)) := by
  constructor
  · intro lm1
    dsimp [getFromLastAt?, getFromEndAt?] at lm1
    split at lm1 <;> rename_i lm2
    · exact Or.inl lm2
    · simp only [ite_eq_right_iff] at lm1
      cases lm3: seq.toEmptyLabel
      · exact Or.inr rfl
      · have lm4 := length_pos_of_nonempty_finite lm3 lm2
        rewrite [Nat.lt_iff_add_one_le] at lm4
        specialize lm1 0 lm4
        dsimp at lm1
        replace lm1 := seq.getAt?_length_sub_add_one_eq_none_iff_empty lm2 |>.mp lm1
        simp [lm1] at lm3
  · intro lm1
    rcases lm1 with lm1 | lm1
    · exact @seq.getFromLastAt?_eq_none_of_infinite _ lm1
    · exact @seq.getFromLastAt?_eq_none_of_empty _ lm1

theorem getFromLastAt?_eq_getAt? (req1: seq.toFinLabel = .finite) {i: ℕ} (req2: i < seq.length req1)
  : (seq.getFromLastAt? i) = (seq.getAt? ((seq.length req1) - (i + 1))) := by
  have lm1 := Nat.lt_iff_add_one_le.mp req2
  dsimp [getFromLastAt?, getFromEndAt?]
  split <;> rename_i lm2
  · simp [lm2] at req1
  · simp only [ite_eq_left_iff]
    intro lm3
    simp at lm3
    replace lm3 := Nat.le_trans lm1 lm3
    simp at lm3

theorem finite_of_getFromLastAt?_isSome {i: ℕ} (req: (seq.getFromLastAt? i).isSome)
  : (seq.toFinLabel = .finite) := by
  have lm2 := Iff.not seq.forall_getFromLastAt?_eq_none_iff_infinite_or_empty
  simp [Option.ne_none_iff_isSome, FiniteLabel.ne_infinite_iff_eq_finite, EmptyLabel.ne_empty_iff_eq_nonempty] at lm2
  replace lm2 := lm2.mp (Exists.intro i req)
  exact lm2.left



theorem getFromLastAt?_eq_of_finite (req: seq.toFinLabel = .finite) {i: ℕ}
  : (seq.getFromLastAt? i) = (if (i + 1) ≤ seq.length req then seq.getAt? (seq.length req - (i + 1)) else .none) := by
  dsimp [getFromLastAt?, getFromEndAt?]
  split <;> rename_i lm1
  · simp [lm1] at req
  · rfl


theorem getFromLastAt?_isSome_iff {i: ℕ}
  : (seq.getFromLastAt? i).isSome ↔ (∃(req: seq.toFinLabel = .finite), i < seq.length req) := by
  constructor
  · intro lm1
    refine Exists.intro ?_ ?_
    · exact seq.finite_of_getFromLastAt?_isSome lm1
    · have lm2 := seq.finite_of_getFromLastAt?_isSome lm1
      revert lm1
      simp only [seq.getFromLastAt?_eq_of_finite lm2]
      split <;> rename_i lm1 <;> intro lm3
      · have lm4 := Nat.le_iff_lt_add_one.mp lm1
        simp at lm4
        exact lm4
      · simp at lm3
  · rintro ⟨lm1, lm2⟩
    rw [getFromLastAt?_eq_of_finite lm1]
    split <;> rename_i lm3
    · clear lm3 /- lm2 = lm3 -/
      have lm3 := seq.lt_length_iff_getAt?_isSome_at lm1
      refine (lm3 _).mp ?_
      refine Nat.sub_lt_self ?_ ?_
      · simp
      · rw [← Nat.lt_iff_add_one_le]
        exact lm2
    · simp at lm3
      have lm4 := Trans.trans lm2 lm3
      simp at lm4


theorem getFromLastAt?_zero_isSome_iff_finite_and_nonempty
  : (seq.getFromLastAt? 0).isSome ↔ ((seq.toFinLabel = .finite) ∧ (seq.toEmptyLabel = .nonempty)) := by
  constructor
  · intro lm1
    have lm2 := seq.getFromLastAt?_isSome_iff.mp lm1
    rcases lm2 with ⟨lm2, lm3⟩
    refine And.intro lm2 ?_
    rewrite [← ENat.coe_lt_coe, ENat.coe_zero, ← (seq.length?_eq_natCast_length lm2)] at lm3
    exact seq.toEmptyLabel_eq_nonempty_iff_length?_pos |>.mpr lm3
  · rintro ⟨lm1, lm2⟩
    refine seq.getFromLastAt?_isSome_iff.mpr ?_
    refine Exists.intro ?_ ?_
    · exact lm1
    · exact length_pos_of_nonempty_finite lm2 lm1


theorem lt_length_iff_getFromLastAt?_isSome (req: seq.toFinLabel = .finite) {i: ℕ}
  : (i < (seq.length req)) ↔ ((seq.getFromLastAt? i).isSome) := by
  have lm1 := seq.lt_length_iff_getAt?_isSome_at req
  have lm2 := @seq.getFromLastAt?_eq_getAt? _ req
  constructor
  · intro lm3
    specialize @lm2 i lm3
    rw [lm2]
    refine (lm1 _).mp ?_
    simp
    calc
      0 ≤ i := Nat.zero_le _
      _ < _ := lm3
  · intro lm3
    rewrite [seq.getFromLastAt?_isSome_iff] at lm3
    rcases lm3 with ⟨lm3, lm4⟩
    exact lm4

theorem length_le_iff_getFromLastAt?_eq_none (req: seq.toFinLabel = .finite) {i: ℕ}
  : (seq.length req ≤ i) ↔ (seq.getFromLastAt? i = .none) := by
  have lm1 := Iff.not (@seq.lt_length_iff_getFromLastAt?_isSome _ req i)
  simpa using lm1


def getFromLastAt (seq: Sequence α) (i: ℕ) (req1: seq.toFinLabel = .finite) (req2: i < (seq.length req1)) : α :=
  seq.getFromLastAt? i |>.get (seq.lt_length_iff_getFromLastAt?_isSome req1 |>.mp req2)

def last? (seq: Sequence α) : Option α := seq.getFromLastAt? 0

def last (seq: Sequence α) (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite) : α :=
  seq.getFromLastAt 0 req2 (seq.length_pos_of_nonempty_finite req1 req2)


theorem last?_eq_some_last (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toFinLabel = .finite)
  : seq.last? = .some (seq.last req1 req2) := by
  dsimp [last?, last, getFromLastAt]
  simp only [Option.some_get]


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



theorem ext_iff : (seq = seq2) ↔ (seq.getAt? = seq2.getAt?) := ⟨congrArg (Sequence.getAt?), Sequence.ext⟩

end Ext



end Sequence

end Nemonuri

end
