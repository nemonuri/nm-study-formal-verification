module

public import Nemonuri.Executions.Basic
public import Nemonuri.SequenceProd.IsWShape.Vector

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

structure IsExecutionFragment.Vector {ts: TransitionSystem} (sp: SequenceProd ts.S ts.Act) (ml: ℕ∞) : Prop extends toBasic: IsExecutionFragment sp where
  minLength?_eq: sp.minLength? = ml

namespace IsExecutionFragment.Vector

variable {ts: TransitionSystem} {sp: SequenceProd ts.S ts.Act} {ml: ℕ∞}

open SequenceProd

theorem isWShape_vector (h: IsExecutionFragment.Vector sp ml) : IsWShape.Vector sp ml := ⟨h.wShape, h.minLength?_eq⟩

theorem of_isWShape_vector_tr
  (req1: IsWShape.Vector sp ml)
  (req2: (i: ℕ) → (req: i < sp.snd.length?) → letI wShape := req1.wShape; (sp.fst.getAt i (wShape.lt_fst_length?_of_lt_snd_length? req)) ─⌞(sp.snd.getAt i req)⌟→{ts} (sp.fst.getAt (i+1) (wShape.add_one_lt_fst_length?_of_lt_snd_length? req)))
  : IsExecutionFragment.Vector sp ml :=
  ⟨⟨req1.wShape, req2⟩, req1.minLength?_eq⟩

end IsExecutionFragment.Vector

structure FiniteExecutionFragmentVector (ts: TransitionSystem) (fml: ℕ) extends toSequenceProd: SequenceProd ts.S ts.Act where
  valid: IsExecutionFragment.Vector toSequenceProd ↑fml



namespace FiniteExecutionFragmentVector

open SequenceProd

def initOf (ts: TransitionSystem) (s: ts.S) : FiniteExecutionFragmentVector ts 0 where
  toSequenceProd := .singleFst ts.S ts.Act s
  valid := by
    refine .of_isWShape_vector_tr ?_ ?_
    · exact .zero_singleFst _ _
    · intro i lm1
      dsimp [singleFst, Sequence.nil_length?_eq_zero] at lm1
      simp at lm1

def lastState {ts: TransitionSystem} {fml: ℕ} (fefv: FiniteExecutionFragmentVector ts fml) : ts.S := fefv.valid.isWShape_vector.lastFst

def stepR {ts: TransitionSystem} (act: ts.Act) (spo: ts.S) {fml: ℕ}
  (fefv: FiniteExecutionFragmentVector ts fml) (req: fefv.lastState ─⌞ act ⌟→{ts} spo)
  : FiniteExecutionFragmentVector ts (fml + 1) where
  toSequenceProd := fefv.toSequenceProd.stepR spo act
  valid := by
    refine .of_isWShape_vector_tr ?_ ?_
    · simp
      refine .add_one_stepR ?_ spo act
      exact fefv.valid.isWShape_vector
    · intro i lm1
      dsimp [SequenceProd.stepR, Sequence.snoc] at lm1
      dsimp [SequenceProd.stepR]
      rcases fefv with ⟨sp, lm3⟩
      rename_i sp2
      subst sp2
      dsimp at ⊢ lm1
      dsimp [lastState, IsWShape.Vector.lastFst] at req
      rcases lm3.wShape.minLength?_eq_iff_eq.mp lm3.minLength?_eq with ⟨lm4, lm5⟩
      rewrite [lm5, ← ENat.coe_one, ← ENat.coe_add, ENat.coe_lt_coe] at lm1
      simp at lm1
      rcases eq_or_lt_of_le lm1 with lm2 | lm2
      · subst lm2
        have lm6 : ↑i < sp.fst.length? := by simp [lm4, ENat.lt_coe_add_one_iff]
        rewrite [(sp.fst.snoc_getAt_eq_getAt i lm6 spo),
                 (sp.snd.snoc_getAt_eq_of_length_eq_natCast i lm5 act),
                 (sp.fst.snoc_getAt_eq_of_length_eq_natCast (i + 1) lm4 spo)]
        rewrite [Sequence.last_eq_getAt] at req
        rewrite [← ENat.coe_one, ← ENat.coe_add] at lm4
        have lm7 := sp.fst.length_eq_of_length?_eq_natCast lm4
        simp [lm7] at req
        exact req
      · have lm6 := lm3.lts_tr
        have lm7 := ENat.coe_lt_coe.mpr lm2
        rewrite [← lm5] at lm7
        specialize lm6 i lm7
        have lm8 := Nat.succ_lt_succ lm2 |> ENat.coe_lt_coe.mpr
        dsimp at lm8
        conv at lm8 =>
          rhs
          rw [ENat.coe_add, ENat.coe_one, ← lm4]
        have lm9 : ↑i < sp.fst.length? := calc
          (↑i: ℕ∞) < ↑(i + 1) := by rw [ENat.coe_lt_coe]; simp
          _ < _ := lm8
        rewrite [(sp.fst.snoc_getAt_eq_getAt i lm9 _),
                 (sp.snd.snoc_getAt_eq_getAt i lm7 _),
                 (sp.fst.snoc_getAt_eq_getAt (i+1) lm8 _)]
        exact lm6

/-
        have lm7 := sp.fst.snoc_getAt_eq_getAt i lm6 spo
        rw [lm7]
        have lm8 := sp.snd.snoc_getAt_eq_of_length_eq_natCast i lm5 act
        rw [lm8]
        have lm9 := sp.fst.snoc_getAt_eq_of_length_eq_natCast (i + 1) lm4 spo
        rw [lm9]
-/

        --have lm6 req := sp.fst.snoc_getAt_eq_getAt i req spo

      --have lm2 := lm3.lts_tr

/-
      have lm4 := lm3.isWShape_vector
      cases lm4 using IsWShape.Vector.recSingleFstStepROn with
      | singleFst s =>
        dsimp [singleFst] at ⊢ lm1
        simp [Sequence.nil_length?_eq_zero] at lm1
        subst lm1
        dsimp [singleFst] at req
        have lm4 req := (Sequence.single s).snoc_getAt_eq_getAt 0 req spo
        simp [Sequence.single_length?_eq_one] at lm4
        rw [lm4, Sequence.single_getAt_zero]
        simp [Sequence.nil_snoc_eq_single]
        rw [Sequence.single_getAt_zero]
        have lm5 := (Sequence.single s).snoc_getAt_eq_of_length_eq_natCast 1 Sequence.single_length?_eq_one spo
        rw [lm5]
        exact req
      | stepR sp fml lm5 s act2 lm_t =>
        clear lm_t
        dsimp [SequenceProd.stepR] at ⊢ lm1 lm2 req
        rewrite [Sequence.snoc_last_eq_of_finite ?h1] at req

        --have lm5 := Sequence.snoc_eq
-/
/-
      rcases fefv.valid.wShape.minLength?_eq_iff_eq.mp (fefv.valid.minLength?_eq) with ⟨lm3, lm4⟩
      simp [lm4] at lm1 lm2
-/



end FiniteExecutionFragmentVector


end Nemonuri.TransitionSystem

end
