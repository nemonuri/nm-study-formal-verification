module

public import Nemonuri.Sequence.Labels

@[expose] public section

namespace Nemonuri

inductive LabelEq (T: Type _) [DecidableEq T] [Fintype T] where
  | labelEq
  | labelNe

namespace LabelEq

variable {T: Type _} [DecidableEq T] [Fintype T]

def beq (l1 l2: LabelEq T) : Bool :=
  match l1, l2 with
  | .labelEq, .labelEq | .labelNe, .labelNe => .true
  | _, _ => .false

instance : DecidableEq (LabelEq T) :=
  fun l1 l2 => decidable_of_bool (beq l1 l2) (by
    dsimp [beq]
    split
    · simp
    · simp
    · rename_i lm1 lm2
      simp
      intro lm3
      subst lm3
      simp at lm1 lm2
      cases l1
      · simp at lm1
      · simp at lm2 )

def enumList (T: Type _) [DecidableEq T] [Fintype T] : List (LabelEq T) := [.labelEq, .labelNe]

theorem enumList_nodup : enumList T |>.Nodup := by
  dsimp [enumList]
  simp

instance : Fintype (LabelEq T) where
  elems := Finset.mk (Multiset.ofList (enumList T)) enumList_nodup
  complete := by
    intro leq
    dsimp [enumList]
    simp
    cases leq <;> simp

theorem ne_labelEq_iff_eq_labelNe {l: LabelEq T}
  : (l ≠ .labelEq) ↔ (l = .labelNe) := by
  cases l <;> simp

theorem ne_labelNe_iff_eq_labelEq {l: LabelEq T}
  : (l ≠ .labelEq) ↔ (l = .labelNe) := by
  cases l <;> simp

section ENat

variable {en1 en2: ℕ∞}

def ofENat (toLabel: ℕ∞ → T) (en1 en2: ℕ∞) : LabelEq T :=
  match decide (toLabel en1 = toLabel en2) with
  | .true => .labelEq
  | .false => .labelNe

def finiteOfENat : ℕ∞ → ℕ∞ → LabelEq FiniteLabel := ofENat FiniteLabel.ofENat

def emptyOfENat : ℕ∞ → ℕ∞ → LabelEq EmptyLabel := ofENat EmptyLabel.ofENat



end ENat

end LabelEq

end Nemonuri

end
