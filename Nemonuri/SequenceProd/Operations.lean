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


end Nemonuri.SequenceProd

end
