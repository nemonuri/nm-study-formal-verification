module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Tactic.DeriveFintype
public import Nemonuri.HasLabel

@[expose] public section

namespace Nemonuri

inductive EmptyLabel where
  | empty
  | nonempty
  deriving DecidableEq, Repr, Fintype

namespace EmptyLabel

theorem ne_empty_iff_eq_nonempty {l: EmptyLabel}
  : (l ≠ .empty) ↔ (l = .nonempty) := by
  cases l <;> simp

theorem ne_nonempty_iff_eq_empty {l: EmptyLabel}
  : (l ≠ .nonempty) ↔ (l = .empty) := by
  cases l <;> simp

@[defeq]
theorem ofNat_zero : EmptyLabel.ofNat 0 = .empty := rfl

@[defeq]
theorem ofNat_succ {n} : EmptyLabel.ofNat (.succ n) = .nonempty := rfl

theorem ofNat_empty_iff_eq_zero {n} : (EmptyLabel.ofNat n = .empty) ↔ (n = 0) := by
  cases n
  · simp [ofNat_zero]
  · simp [ofNat_succ]


def ofENat (en: ENat) : EmptyLabel := ENat.recTopCoe (EmptyLabel.nonempty) (fun n => EmptyLabel.ofNat n) en

@[defeq]
theorem ofENat_natCast {n} : ofENat (Nat.cast n) = ofNat n := rfl

@[defeq]
theorem ofENat_zero : ofENat 0 = .empty := rfl

@[defeq]
theorem ofENat_succ {n} : ofENat (Nat.succ n) = .nonempty := rfl

@[defeq]
theorem ofENat_top : ofENat ⊤ = .nonempty := rfl

theorem ofENat_empty_iff_eq_zero {n: ENat} : (EmptyLabel.ofENat n = .empty) ↔ (n = 0) := by
  cases n
  · simp [ofENat_top]
  · simp [ofENat_natCast]
    exact ofNat_empty_iff_eq_zero

theorem ofENat_nonempty_iff_pos {n: ENat} : (EmptyLabel.ofENat n = .nonempty) ↔ (0 < n) := by
  have lm1 := @ofENat_empty_iff_eq_zero n
  cases lm2: EmptyLabel.ofENat n
  · simp; exact lm1.mp lm2
  · rw [lm2] at lm1
    cases n
    · simp
    · simp at lm1 ⊢
      exact Nat.pos_of_ne_zero lm1



scoped instance : HasLabel EmptyLabel Nat := ⟨ofNat⟩

scoped instance : HasLabel EmptyLabel ENat := ⟨ofENat⟩

attribute [scoped simp] ofNat_zero ofNat_succ ofENat_natCast ofENat_zero ofENat_succ ofENat_top


section List

variable {α: Type _} {a: α} {as: List α}

def ofList (as: List α) : EmptyLabel := match as with | .nil => .empty | .cons _ _ => .nonempty

@[defeq]
theorem ofList_nil : (ofList ([]: List α)) = .empty := rfl

@[defeq]
theorem ofList_cons : (ofList (a::as)) = .nonempty := rfl

scoped instance : HasLabel EmptyLabel (List α) := ⟨ofList⟩

attribute [scoped simp] ofList_nil ofList_cons

theorem ofList_eq_empty_iff_eq_nil : ((ofList as) = .empty) ↔ (as = []) := by
  cases as <;> simp

theorem ofList_eq_empty_iff_length_eq_zero : ((ofList as) = .empty) ↔ (as.length = 0) :=
  calc
    _ ↔ _ := ofList_eq_empty_iff_eq_nil
    _ ↔ _ := List.eq_nil_iff_length_eq_zero

theorem ofList_eq_nonempty_iff_ne_nil : ((ofList as) = .nonempty) ↔ (as ≠ []) := by
  cases as <;> simp

theorem ofList_eq_nonempty_iff_length_pos : ((ofList as) = .nonempty) ↔ (0 < as.length) :=
  calc
    _ ↔ _ := ofList_eq_nonempty_iff_ne_nil
    _ ↔ _ := List.ne_nil_iff_length_pos

theorem ofList_eq_ofNat : (ofList as) = (ofNat as.length) := by
  cases as <;> simp

end List

end EmptyLabel

inductive FiniteLabel where
  | finite
  | infinite
  deriving DecidableEq, Repr, Fintype

namespace FiniteLabel

theorem ne_finite_iff_eq_infinite {l: FiniteLabel}
  : (l ≠ .finite) ↔ (l = .infinite) := by
  cases l <;> simp

theorem ne_infinite_iff_eq_finite {l: FiniteLabel}
  : (l ≠ .infinite) ↔ (l = .finite) := by
  cases l <;> simp

variable {en: ENat} {n: Nat}

def ofENat (en: ENat) : FiniteLabel := en.recTopCoe .infinite (fun _ => .finite)

@[defeq]
theorem ofENat_top : ofENat ⊤ = .infinite := rfl

@[defeq]
theorem ofENat_natCast : ofENat (Nat.cast n) = .finite := rfl

attribute [scoped simp] ofENat_top ofENat_natCast

theorem ofENat_infinite_iff_eq_top : (ofENat en = .infinite) ↔ (en = ⊤) := by
  cases en <;> simp

theorem ofENat_finite_iff_lt_top : (ofENat en = .finite) ↔ (en < ⊤) := by
  cases en <;> simp

theorem ofENat_finite_iff_ne_top : (ofENat en = .finite) ↔ (en ≠ ⊤) := by
  cases en <;> simp

theorem ofENat_finite_iff_eq_natCast : (ofENat en = .finite) ↔ ∃(n: Nat), (en = Nat.cast n) := by
  cases en <;> simp


end FiniteLabel

end Nemonuri

end
