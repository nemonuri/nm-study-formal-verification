module

public import Nemonuri.SequenceProd.IsWShape.Operations


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.SequenceProd.IsWShape

variable {α β: Type*}

structure Vector (sp: SequenceProd α β) (ml: ℕ∞) : Prop where
  wShape : sp.IsWShape
  minLength?_eq : sp.minLength? = ml

namespace Vector

variable (β) in
theorem zero_singleFst (a: α) : IsWShape.Vector (singleFst α β a) 0 where
  wShape := .of_singleFst
  minLength?_eq := by
    rw [IsWShape.minLength?_eq_snd_length? .of_singleFst]
    dsimp [singleFst, Sequence.nil]


theorem headFst_singleFst_eq_self_of_zero {sp: SequenceProd α β} (h: IsWShape.Vector sp 0) : (singleFst α β h.wShape.headFst) = sp := h.wShape.singleFst_eq_self_of_minLength?_eq_zero h.minLength?_eq

variable {sp: SequenceProd α β} {ml: ℕ∞}

theorem add_one_stepR (h: IsWShape.Vector sp ml) (a: α) (b: β) : IsWShape.Vector (sp.stepR a b) (ml + 1) := by
  rcases h with ⟨lm1, lm2⟩
  have lm3 := lm1.stepR_isWShape a b
  refine .mk lm3 ?_
  rw [← lm2, lm1.minLength?_eq_snd_length?, lm3.minLength?_eq_snd_length?]
  dsimp [stepR, Sequence.snoc]

theorem dropLast_of_add_one_natCast {fml: ℕ} (h: IsWShape.Vector sp ↑(fml + 1)) : IsWShape.Vector sp.dropLast ↑fml := by
  rcases h with ⟨lm1, lm2⟩
  rcases lm1.minLength?_eq_iff_eq.mp lm2 with ⟨lm3, lm4⟩
  have lm5 : IsWShape sp.dropLast := by
    refine lm1.dropLast_isWShape_of_minLength?_post ?_
    rw [lm2]
    simp
  refine ⟨lm5, ?_⟩
  rw [lm5.minLength?_eq_snd_length?]
  dsimp [SequenceProd.dropLast, Sequence.dropLast]
  rw [lm4, ← ENat.coe_one, ← ENat.coe_sub, ENat.coe_inj]
  exact Nat.add_one_sub_one _


/-
theorem takeW_vector_of_le_at (h: IsWShape.Vector sp ml) (n: ℕ) (req: ↑n < ml) : IsWShape.Vector (sp.takeW n) n := by
  have lm1 := h.wShape.takeW_isWShape_at n
  refine ⟨lm1, ?_⟩
  rw [lm1.minLength?_eq_snd_length?]
  dsimp [takeW, take, Sequence.take]
  have lm2 := h.minLength_eq
  rewrite [h.wShape.minLength?_eq_snd_length?] at lm2
  rw [lm2]
  simp
  intro lm3
  have lm4 := Trans.trans req lm3
  simp at lm4
-/


@[elab_as_elim]
def recSingleFstStepR.{u}
  {motive: (sp: SequenceProd α β) → (fml: ℕ) → IsWShape.Vector sp ↑fml → Sort u}
  (singleFst: (a: α) → motive (singleFst α β a) 0 (zero_singleFst β a))
  (stepR: (sp: SequenceProd α β) → (fml: ℕ) → (req: IsWShape.Vector sp ↑fml) → (a: α) → (b: β) → motive sp ↑fml req → motive (sp.stepR a b) (↑(fml + 1)) (req.add_one_stepR a b))
  (sp: SequenceProd α β) (fml: ℕ) (h: IsWShape.Vector sp ↑fml)
  : motive sp ↑fml h :=
  match fml with
  | 0 =>
    singleFst (h.wShape.headFst) |> cast (by
      congr
      exact h.headFst_singleFst_eq_self_of_zero)
  | fml + 1 =>
    have lm1 : 0 < sp.minLength? := by rw [h.minLength?_eq]; simp
    have lm2 : h.wShape.toFiniteLabel = .finite := by
      have lm2_1 := h.minLength?_eq
      refine h.wShape.finite_iff_minLength?_eq_natCast.mpr ?_
      exact Exists.intro _ lm2_1
    let v := h.wShape.last lm1 lm2
    let sp2 := sp.dropLast
    stepR sp2 fml h.dropLast_of_add_one_natCast v.fst v.snd (recSingleFstStepR singleFst stepR sp2 fml h.dropLast_of_add_one_natCast) |> cast (by
      congr
      subst v sp2
      dsimp [IsWShape.last]
      exact sp.last_dropLast_stepR_eq_self _ _ _ _ )

@[elab_as_elim]
def recSingleFstStepROn.{u}
  {motive: (sp: SequenceProd α β) → (fml: ℕ) → IsWShape.Vector sp ↑fml → Sort u}
  {sp: SequenceProd α β} {fml: ℕ} (h: IsWShape.Vector sp ↑fml)
  (singleFst: (a: α) → motive (singleFst α β a) 0 (zero_singleFst β a))
  (stepR: (sp: SequenceProd α β) → (fml: ℕ) → (req: IsWShape.Vector sp ↑fml) → (a: α) → (b: β) → motive sp ↑fml req → motive (sp.stepR a b) (↑(fml + 1)) (req.add_one_stepR a b))
  : motive sp ↑fml h :=
  recSingleFstStepR singleFst stepR sp fml h



/-
    have lm3 : (↑fml: ℕ∞) < ↑(fml + 1) := by rw [ENat.coe_lt_coe]; simp
    stepR sp2 fml (h.takeW_vector_of_le_at fml lm3) v.fst v.snd (recSingleFstStepR singleFst stepR sp2 fml (h.takeW_vector_of_le_at fml lm5)) |> cast (by
      congr
      subst v sp2
      dsimp [IsWShape.last]
      rcases h with ⟨lm4, lm5⟩
-/
      --rcases sp with ⟨seq1, seq2⟩
      --dsimp [SequenceProd.stepR]
      --congr
      --rewrite [lm4.minLength?_eq_snd_length?] at lm5


    --stepR sp fml
    --let ⟨a, b⟩ := h.wShape.last
/-
  match fml with
  | 0 =>
    let a : α := sp.fst.head (h.wShape.fst_nonempty)
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
  | fml + 1 =>
-/

def lastFst {fml: ℕ} (req: IsWShape.Vector sp ↑fml) : α := sp.fst.last req.wShape.fst_nonempty (by
    have lm1 := req.minLength?_eq
    replace lm1 := congrArg (· + 1) lm1
    rw [req.wShape.minLength?_add_one_eq_fst_length?] at lm1
    refine sp.fst.finite_iff_length?_eq_natCast.mpr ?_
    exists (fml + 1) )

end Vector

end Nemonuri.SequenceProd.IsWShape

end
