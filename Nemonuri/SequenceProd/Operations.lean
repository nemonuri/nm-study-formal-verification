module

public import Nemonuri.SequenceProd.Basic
public import Nemonuri.Sequence.Operations

@[expose] public section

namespace Nemonuri.SequenceProd

open Sequence

variable {α: Type _} {β: Type _} {sp sp2: SequenceProd α β} {a: α} {b: β}


def singleFst (α β: Type _) (a: α) : SequenceProd α β := ⟨Sequence.single a, Sequence.nil⟩

section SingleFst

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

theorem singleFst_getAt?_zero : (singleFst α β a).getAt? 0 = OptionProd.fst a := by
  refine OptionProd.ext ?_ ?_ <;> dsimp [singleFst, getAt?_eq_ofProd?_getAt?]
  . simp
    dsimp [Sequence.single]
  · simp
    exact Sequence.nil_getAt?_none

theorem singleFst_getAt?_add_one {i: ℕ} : (singleFst α β a).getAt? (i + 1) = OptionProd.none := by
  refine OptionProd.ext ?_ ?_ <;> dsimp [singleFst, getAt?_eq_ofProd?_getAt?]
  · simp
    dsimp [Sequence.single]
  · simp
    exact Sequence.nil_getAt?_none

end SingleFst


def stepL (a: α) (b: β) : SequenceProd α β → SequenceProd α β
  | ⟨fst, snd⟩ => ⟨Sequence.cons a fst, Sequence.cons b snd⟩

section StepL

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

theorem stepL_getAt?_zero : (sp.stepL a b).getAt? 0 = OptionProd.both a b := by
  rw [← getAt?Flip_eq_getAt?]
  rw [← head?_eq_getAt?Flip_zero]
  exact stepL_head?

theorem stepL_getAt?_add_one_at (i: ℕ) : (sp.stepL a b).getAt? (i + 1) = sp.getAt? i := by
  simp only [getAt?_eq_ofProd?_getAt?]
  refine congrArg _ ?_
  refine Prod.ext ?_ ?_ <;> dsimp [stepL]
  <;> exact Sequence.cons_getAt?_add_one_eq_getAt?

end StepL


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



def nil : SequenceProd α β := ⟨Sequence.nil, Sequence.nil⟩

section Nil

theorem nil_finiteEq : (nil: SequenceProd α β).toFiniteLabelEq = .labelEq := by
  rw [finiteEq_iff_fst_snd_finiteEq]
  dsimp [nil]
  rfl

theorem nil_finite : (nil: SequenceProd α β).toFiniteLabel nil_finiteEq = .finite := by
  rw [← fst_self_finiteEq]
  dsimp [nil]
  exact Sequence.nil_finite

@[defeq]
theorem nil_getAt? {i: ℕ} : (nil: SequenceProd α β).getAt? i = OptionProd.none := rfl

end Nil


def append (sp1: SequenceProd α β) (req1: sp1.toFiniteLabelEq = .labelEq) (req2: sp1.toFiniteLabel req1 = .finite) (sp2: SequenceProd α β) : SequenceProd α β :=
  have lm1 := sp1.finite_congr_of_finiteEq req1 |>.mp req2
  ⟨sp1.fst.append lm1.left sp2.fst, sp1.snd.append lm1.right sp2.snd⟩

section Append

variable {sp1 sp2: SequenceProd α β} {req1: sp1.toFiniteLabelEq = .labelEq} {req2: sp1.toFiniteLabel req1 = .finite} {i: ℕ}

theorem append_nil_eq_id : (nil: SequenceProd α β).append nil_finiteEq nil_finite = id := by
  refine funext ?_
  intro sp
  dsimp [nil, append]
  congr <;> simp [Sequence.append_nil_eq_id]

theorem append_self_nil_eq_self (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite)
  : sp.append req1 req2 nil = sp := by
  refine prod_ext ?_ ?_ <;> dsimp [nil, append] <;> simp [Sequence.append_self_nil_eq_self]

theorem append_getAt?_of_lt_length (req3: i < sp1.minLength?)
  : (sp1.append req1 req2 sp2).getAt? i = sp1.getAt? i := by
  rewrite [sp1.lt_minLength?_iff_lt_length?] at req3
  rcases req3 with ⟨lm1, lm2⟩
  dsimp [append]
  repeat rw [SequenceProd.getAt?_eq_ofProd?_getAt?]
  dsimp
  refine OptionProd.ext ?_ ?_ <;> simp
  · refine Sequence.append_getAt?_of_lt_length ?_
    rw [← ENat.coe_lt_coe, ← Sequence.length?_eq_natCast_length]
    exact lm1
  · refine Sequence.append_getAt?_of_lt_length ?_
    rw [← ENat.coe_lt_coe, ← Sequence.length?_eq_natCast_length]
    exact lm2


end Append




def stepL? (o: OptionProd α β) (sp: SequenceProd α β) : SequenceProd α β := ⟨Sequence.cons? o.fst? sp.fst, Sequence.cons? o.snd? sp.snd⟩

end Nemonuri.SequenceProd

end
