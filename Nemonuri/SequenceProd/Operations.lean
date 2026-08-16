module

public import Nemonuri.SequenceProd.Basic
public import Nemonuri.Sequence.Operations

@[expose] public section

namespace Nemonuri.SequenceProd

open Sequence

variable {α: Type _} {β: Type _} {sp sp2: SequenceProd α β} {a: α} {b: β}


def singleFst (α β: Type _) (a: α) : SequenceProd α β := ⟨Sequence.single a, Sequence.nil⟩

theorem singleFst_toFinLabelEq {a: α} : (singleFst α β a).toFinLabelEq = .eq := by
  rw [toFinLabel_eq_eq_iff]
  dsimp [singleFst]
  dsimp [Sequence.toFinLabel]
  rw [Sequence.single_length?_eq_one, Sequence.nil_length?_eq_zero]
  rw [← ENat.coe_one, ← ENat.coe_zero]
  simp only [FiniteLabel.ofENat_natCast]

theorem singleFst_toFinLabel {a: α} : (singleFst α β a).toFinLabel singleFst_toFinLabelEq = .finite := by
  rw [tofinLabel_eq_snd_toFinLabel]
  dsimp [singleFst]
  refine Sequence.finite_of_empty ?_
  rw [Sequence.toEmptyLabel_eq_empty_iff_length?_eq_zero]
  exact nil_length?_eq_zero


def stepL (a: α) (b: β) : SequenceProd α β → SequenceProd α β
  | ⟨fst, snd⟩ => ⟨Sequence.cons a fst, Sequence.cons b snd⟩

theorem stepL_emptyLabel_eq : (sp.stepL a b).toEmptyLabelEq = .eq := by
  rw [toEmptyLabel_eq_eq_iff]
  dsimp [stepL]
  simp only [Sequence.cons_nonempty]

theorem stepL_nonempty : (sp.stepL a b).toEmptyLabel stepL_emptyLabel_eq = .nonempty := by
  rw [toEmptyLabel_eq_fst_toEmptyLabel]
  dsimp [stepL]
  simp only [Sequence.cons_nonempty]

theorem stepL_head? : (sp.stepL a b).head? = OptionProd.both a b := by
  rw [head?_eq_ofProd?]
  refine OptionProd.ext ?_ ?_
  <;> (simp; dsimp [stepL]; exact cons_head?)

theorem stepL_head : (sp.stepL a b).head stepL_emptyLabel_eq stepL_nonempty = (a, b) := by
  rw [← OptionProd.ofProd_injective.eq_iff]
  rw [← SequenceProd.head?_eq_ofProd_head]
  refine stepL_head?.trans ?_
  dsimp


def tail : SequenceProd α β → SequenceProd α β
  | ⟨fst, snd⟩ => ⟨fst.tail, snd.tail⟩

theorem stepL_tail : (sp.stepL a b).tail = sp := by
  refine SequenceProd.ext ?_ ?_
  <;> dsimp [tail, stepL]
  <;> rw [← Sequence.ext_iff]
  <;> exact Sequence.cons_tail

/-
theorem stepL_eta (req1: sp.toEmptyLabelEq = .eq) (req2: sp.toEmptyLabel req1 = .nonempty)
  : let x := sp.head req1 req2; stepL x.fst x.snd sp.tail = sp := by
  extract_lets x
  rcases lm1: x with ⟨a, b⟩
  subst x
  dsimp
  rewrite [Prod.ext_iff] at lm1
  rcases lm1 with ⟨lm1, lm2⟩
  dsimp at lm1 lm2
  refine SequenceProd.ext ?_ ?_
  <;> rw [← Sequence.ext_iff]
  <;> dsimp [tail, stepL]
  <;> rw [Sequence.tail_cons_eq_self_iff]
  · refine Exists.intro ?_ ?_
    ·
-/


/-
theorem stepL_head : (sp.stepL a b).head stepL_toEmptyLabelEq stepL_toEmptyLabel = (a, b) := by
  dsimp [head]
  refine Prod.ext ?_ ?_ <;>
  dsimp [stepL]
  exact Sequence.cons_head?
-/

end Nemonuri.SequenceProd

end
