module

public import Mathlib.Order.Defs.Unbundled

@[expose] public section

set_option autoImplicit false

namespace Nemonuri

structure IsQuotientNormalizer {α: Type _} (s: Setoid α) (op: α → α) : Prop where
  apply_eq (a1 a2: α) (req: s.r a1 a2) : (op a1) = (op a2)
  apply_rel (a: α) : s.r a (op a)
  --idem (a: α) : f (f a) = f a
  --liftable (a1 a2: α) (req: s.r a1 a2) : f a1 = f a2

@[defeq, simp]
protected theorem setoid_hasEquiv_def {α: Type _} {s: Setoid α} {a1 a2: α} : (a1 ≈ a2) = (s.r a1 a2) := rfl

namespace IsQuotientNormalizer

variable {α: Type _} {s: Setoid α} {op: α → α}

theorem idempotent (h: IsQuotientNormalizer s op) {a: α} : (op (op a)) = op a :=
  (h.apply_eq a (op a) (h.apply_rel a)).symm

theorem apply_eq_iff (h: IsQuotientNormalizer s op) {a1 a2: α} : ((op a1) = (op a2)) ↔ (s.r a1 a2) := by
  have lm_tr : IsTrans _ s.r := s.iseqv.isTrans
  constructor
  · intro lm1
    have lm2 := h.apply_rel (op a1)
    conv at lm2 => arg 2; rw [lm1, h.idempotent]
    simp
    calc
      s.r _ _ := h.apply_rel a1
      s.r _ _ := lm2
      s.r _ _ := h.apply_rel a2 |> s.symm
  · exact h.apply_eq _ _

theorem apply_eq_iff_at (h: IsQuotientNormalizer s op) (a1 a2: α) : ((op a1) = (op a2)) ↔ (s.r a1 a2) := h.apply_eq_iff

def normalize (h: IsQuotientNormalizer s op) (q: Quotient s) : α := q.liftOn op (h.apply_eq)

end IsQuotientNormalizer

structure QuotientNormalizer {α: Type _} (s: Setoid α) where
  op: α → α
  valid: IsQuotientNormalizer s op


namespace QuotientNormalizer

variable {α: Type _} {s: Setoid α}

def normalize (x: QuotientNormalizer s) (q: Quotient s) : α := x.valid.normalize q


end QuotientNormalizer


end Nemonuri

end
