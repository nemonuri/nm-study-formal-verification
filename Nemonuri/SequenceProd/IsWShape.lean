module

public import Nemonuri.SequenceProd.Basic

@[expose] public section

namespace Nemonuri.SequenceProd

variable {α β: Type _}

def IsWShape (sp: SequenceProd α β) : Prop := sp.fst.length? = sp.snd.length? + 1

namespace IsWShape

variable {α β: Type _} {sp: SequenceProd α β}

theorem mk (length?_eq: sp.fst.length? = sp.snd.length? + 1) : IsWShape sp := length?_eq

theorem length?_eq (h: IsWShape sp) : sp.fst.length? = sp.snd.length? + 1 := h



theorem finite_eq (h: IsWShape sp) : sp.toFiniteLabelEq = .labelEq := by
  rw [sp.finiteEq_iff_fst_snd_finiteEq]
  cases lm1: sp.fst.toFiniteLabel
  · rewrite [sp.fst.finite_iff_length?_eq_natCast] at lm1
    rcases lm1 with ⟨n, lm1⟩
    rewrite [h.length?_eq] at lm1
    symm
    rw [sp.snd.finite_iff_length?_eq_natCast]
    exists (n - 1)
    rcases n with _ | n
    · simp at lm1
    · simp at lm1 ⊢
      rw [lm1]
  · symm
    rewrite [Sequence.infinite_iff_length?_eq_top] at lm1 ⊢
    rewrite [h.length?_eq] at lm1
    have lm2 {a b : ℕ∞} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top
    rewrite [lm2] at lm1
    simp at lm1
    exact lm1


theorem add_one_lt_fst_length?_of_lt_snd_length? (h: IsWShape sp) {i: ℕ} (req: i < sp.snd.length?) : i + 1 < sp.fst.length? := by
  rw [h.length?_eq]
  refine ENat.add_lt_add_iff_right ?_ |>.mpr req
  simp

theorem lt_fst_length?_of_lt_snd_length? (h: IsWShape sp) {i: ℕ} (req: i < sp.snd.length?) : i < sp.fst.length? :=
  calc
    (i: ℕ∞) < (i: ℕ∞) + 1 := by rw [← ENat.coe_one, ← ENat.coe_add, ENat.coe_lt_coe]; exact Nat.lt_add_one i
    _ < _ := h.add_one_lt_fst_length?_of_lt_snd_length? req


theorem fst_nonempty (h: IsWShape sp) : sp.fst.toEmptyLabel = .nonempty := by
  rw [sp.fst.nonempty_iff_length?_ne_zero]
  rw [h.length?_eq]
  simp



end IsWShape


end Nemonuri.SequenceProd

end
