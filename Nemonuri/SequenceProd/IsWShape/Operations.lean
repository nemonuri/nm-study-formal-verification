module

public import Nemonuri.SequenceProd.IsWShape.Basic
public import Nemonuri.SequenceProd.Operations

@[expose] public section

namespace Nemonuri.SequenceProd.IsWShape

variable {α β: Type _}  {sp sp2: SequenceProd α β} {a: α} {b: β}

theorem of_singleFst : (singleFst α β a).IsWShape := by
  refine .mk ?_
  dsimp [singleFst]
  rw [Sequence.single_length?_eq_one, Sequence.nil_length?_eq_zero]
  simp

/-
    singleFst a |> cast (by
      subst a
      congr
      rcases sp with ⟨seq1, seq2⟩
      dsimp [SequenceProd.singleFst]
      congr
      · refine Sequence.ext ?_
        refine funext ?_
        intro i
        cases i with
        | zero =>
          have lm1 := h.wShape.fst_nonempty
          dsimp at lm1
          have lm2 := seq1.head?_eq_some_head lm1
          dsimp [Sequence.single_getAt?_zero]
          refine Eq.trans lm2.symm ?_
          exact seq1.head?_eq_getAt?_zero
        | succ i =>
          simp [Sequence.single_getAt?_add_one]
          rcases h with ⟨lm1, lm2⟩
          have lm3 := lm1.minLength?_add_one_eq_fst_length?
          simp [lm2] at lm3
          have lm4 := seq1.length_le_iff_getAt?_eq_none_at ?h1 (i + 1)
          case h1 => exact seq1.finite_of_length?_eq_natCast lm3.symm
          symm
          refine lm4.mp ?_
          dsimp [Sequence.length_eq_length?_lift]
          simp [← lm3]
      · refine Sequence.ext ?_
        refine funext ?_
        intro i
        dsimp [Sequence.nil_getAt?_none]
        have lm1 := h.minLength_eq
        rewrite [h.wShape.minLength?_eq_snd_length?] at lm1
        dsimp at lm1
        replace lm1 := Sequence.empty_iff_length?_eq_zero.mpr lm1
        replace lm1 := Sequence.empty_iff_forall_getAt?_eq_none.mp lm1 i
        exact lm1.symm )
-/

/-
theorem minLength?_eq_zero_iff_eq_singleFst_head (h: sp.IsWShape) : (sp.minLength? = 0) ↔ (singleFst α β (sp.fst.head h.fst_nonempty) = sp) := by
  rw [h.minLength?_eq_snd_length?]
  rcases sp with ⟨seq1, seq2⟩
  simp [singleFst]
  constructor
  · intro lm1
    dsimp [IsWShape] at h
    revert h
    simp [lm1]
    intro h
    have lm2 := seq2.empty_iff_length?_eq_zero.mpr lm1
    rw [← Sequence.eq_nil_iff_empty] at lm2
    refine ⟨?_, lm2.symm⟩
-/

  --
  --constructor
  --· intro lm1


theorem stepL_iff : (sp.stepL a b).IsWShape ↔ sp.IsWShape := by
  constructor
  · intro lm1
    refine .mk ?_
    have lm2 := lm1.length?_eq
    dsimp [stepL] at lm2
    simp [Sequence.cons_length?_eq_length?_add_one] at lm2
    exact lm2
  · intro lm1
    refine .mk ?_
    have lm2 := lm1.length?_eq
    dsimp [stepL]
    simp [Sequence.cons_length?_eq_length?_add_one]
    exact lm2



theorem not_nil : ¬(nil: SequenceProd α β).IsWShape := by
  intro lm1
  dsimp [nil] at lm1
  replace lm1 := lm1.fst_nonempty
  dsimp at lm1
  simp [Sequence.nil_empty] at lm1


theorem stepR_iff : (sp.stepR a b).IsWShape ↔ sp.IsWShape := by
  dsimp [IsWShape, stepR, Sequence.snoc]
  simp


theorem stepR_isWShape (h: sp.IsWShape) (a: α) (b: β) : (sp.stepR a b).IsWShape := stepR_iff.mpr h


def headFst (h: sp.IsWShape) : α := sp.fst.head (h.fst_nonempty)

@[defeq]
theorem headFst_def {h: sp.IsWShape} : h.headFst = sp.fst.head h.fst_nonempty := rfl

theorem singleFst_eq_self_of_minLength?_eq_zero (h: sp.IsWShape) (req: sp.minLength? = 0) : singleFst α β h.headFst = sp := by
  dsimp [singleFst]
  rewrite [h.minLength?_eq_snd_length?] at req
  dsimp [headFst_def]
  revert h
  simp [IsWShape, req]
  intro lm1
  congr
  · exact Sequence.head_single_eq_self_of_length?_eq_one lm1
  · symm
    exact Sequence.length?_eq_zero_iff_eq_nil.mp req


def last (h: IsWShape sp) (req1: 0 < sp.minLength?) (req2: h.toFiniteLabel = .finite) : (α × β) :=
  have lm1 := sp.nonempty_of_minLength?_pos req1
  sp.last h.finite_eq req2 lm1.fst lm1.snd


theorem dropLast_isWShape_of_minLength?_post (h: IsWShape sp) (req: 0 < sp.minLength?) : IsWShape (sp.dropLast) := by
  rewrite [sp.minLength?_pos_iff_length?_pos] at req
  rcases req with ⟨lm1, lm2⟩
  dsimp [IsWShape, dropLast, Sequence.dropLast]
  rw [h.length?_eq]
  generalize lm3: sp.snd.length? = en
  rewrite [lm3] at lm2
  cases en with
  | top => simp
  | coe n =>
    simp at lm2
    conv =>
      rw [← ENat.coe_one]
      conv =>
        lhs
        rw [← ENat.coe_add, ← ENat.coe_sub]
      conv =>
        rhs
        rw [← ENat.coe_sub, ← ENat.coe_add]
      rw [ENat.coe_inj]
    rw [Nat.sub_one_add_one_eq_of_pos lm2]
    exact Nat.add_one_sub_one n


def lastFst (h: IsWShape sp) (req: h.toFiniteLabel = .finite) : α := sp.fst.last h.fst_nonempty (h.finite_iff_fst_finite.mp req)




/-
  have lm_fin1 := h.finite_iff_fst_finite.mp req2
  have lm_fin2 := h.finite_iff_snd_finite.mp req2
  let v1 : α := sp.fst.last (h.fst_nonempty) lm_fin1
  let v2 : β := sp.snd.last (sp.snd.nonempty_iff_length?_pos.mpr (h.minLength?_eq_snd_length? ▸ req1)) lm_fin2
  ⟨v1, v2⟩
-/

/-
theorem takeW_isWShape_at (h: IsWShape sp) (n: ℕ) : IsWShape (sp.takeW n) := by
  have lm1 := h.length?_eq
  dsimp [takeW, take, IsWShape, Sequence.take]
  simp [lm1]
  rcases n with _ | ⟨n⟩
  · simp
  · split <;> simp
-/

--variable (sp) in
/-
  have lm2 := h.length?_eq
  have lm3 := ENat.coe_inj.mpr lm1
  rewrite [← sp.minLength?_eq_natCast_minLength, h.minLength?_eq_snd_length?] at lm3
  rewrite [lm3] at lm2 --, ← ENat.coe_one, ← ENat.coe_add
  rcases sp with ⟨seq1, seq2⟩
  dsimp at lm2 lm3
  cases lm3 using Sequence.recLengthEqRevOn with
  | zero =>
    rewrite [h.minLength?_eq_snd_length?] at req1
    dsimp [Sequence.nil_length?_eq_zero] at req1
    simp only [lt_self_iff_false] at req1
  | succ b seq2 len lm3 lm4 =>
    clear lm4
    simp
    have lm5 := congrArg (Nat.pred) lm1
    simp at lm5 lm2
    cases lm2 using Sequence.recLengthEqRevOn with
    | succ a seq1 _ lm2 lm4 =>
      clear lm4
      simp at lm2
      --let sp : SequenceProd α β := ⟨seq1, seq2⟩
      dsimp [takeW, take, stepR, IsWShape.last]
      simp
-/
    --have lm5 := takeW_last_stepR_eq_self h
  --cases lm3 using Sequence.recLengthEqRevOn
  --dsimp [SequenceProd.minLength] at lm1


/-
  simp [← Sequence.takeRec_eq_take]
  dsimp [Sequence.takeRec]
  simp [h.fst_nonempty, Sequence.cons_length?_eq_length?_add_one]
  simp [Sequence.takeRec_eq_take]
  dsimp [Sequence.take]
  have lm2 := sp.fst.tail_length?_eq_length?_sub_one
-/
  --have lm2 := sp.fst.tail_length?_eq_length?_sub_one
  --rw [← Sequence.takeRec_eq_take]
  --, IsWShape



end Nemonuri.SequenceProd.IsWShape

end
