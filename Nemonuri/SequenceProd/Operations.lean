module

public import Nemonuri.SequenceProd.Basic
public import Nemonuri.Sequence.Operations

@[expose] public section

namespace Nemonuri.SequenceProd

open Sequence

variable {α: Type _} {β: Type _} {sp sp2: SequenceProd α β} {a: α} {b: β}


def singleFst (α β: Type _) (a: α) : SequenceProd α β := ⟨Sequence.single a, Sequence.nil⟩

theorem singleFst_finiteEq {a: α} : (singleFst α β a).toFiniteLabelEq = .labelEq := by
  rw [finiteEq_iff_fst_snd_finiteEq]
  dsimp [singleFst]
  dsimp [Sequence.toFiniteLabel]
  rw [Sequence.single_length?_eq_one, Sequence.nil_length?_eq_zero]
  rw [← ENat.coe_one, ← ENat.coe_zero]
  simp only [FiniteLabel.ofENat_natCast]

theorem singleFst_toFinLabel {a: α} : (singleFst α β a).toFiniteLabel singleFst_finiteEq = .finite := by
  rw [← snd_self_finiteEq]
  dsimp [singleFst]
  refine Sequence.finite_of_empty ?_
  rw [Sequence.empty_iff_length?_eq_zero]
  exact nil_length?_eq_zero


def stepL (a: α) (b: β) : SequenceProd α β → SequenceProd α β
  | ⟨fst, snd⟩ => ⟨Sequence.cons a fst, Sequence.cons b snd⟩

theorem stepL_emptyLabel_eq : (sp.stepL a b).toEmptyLabelEq = .labelEq := by
  rw [emptyEq_iff_fst_snd_emptyEq]
  dsimp [stepL]
  simp only [Sequence.cons_nonempty]

theorem stepL_nonempty : (sp.stepL a b).toEmptyLabel stepL_emptyLabel_eq = .nonempty := by
  rw [← fst_self_emptyEq]
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


theorem stepL_eta (req1: sp.toEmptyLabelEq = .labelEq) (req2: sp.toEmptyLabel req1 = .nonempty)
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
    · have lm3 := fst_self_emptyEq req1 |>.symm
      calc
        _ = _ := lm3.symm
        _ = _ := req2
    · rw [← lm1]
      dsimp [head]
  · refine Exists.intro ?_ ?_
    · have lm3 := snd_self_emptyEq req1 |>.symm
      calc
        _ = _ := lm3.symm
        _ = _ := req2
    · rw [← lm2]
      dsimp [head]



/-
theorem stepL_head : (sp.stepL a b).head stepL_toEmptyLabelEq stepL_toEmptyLabel = (a, b) := by
  dsimp [head]
  refine Prod.ext ?_ ?_ <;>
  dsimp [stepL]
  exact Sequence.cons_head?
-/

end Nemonuri.SequenceProd

end
