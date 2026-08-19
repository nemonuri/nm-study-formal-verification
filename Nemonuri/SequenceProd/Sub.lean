module

public import Nemonuri.SequenceProd.Operations
public import Nemonuri.Sequence.Sub

@[expose] public section

namespace Nemonuri.SequenceProd

variable {α β: Type _}

@[mk_iff]
inductive IsPrefix (sp1: SequenceProd α β) : SequenceProd α β → Prop where
  | intro (req1: sp1.toFiniteLabelEq = .labelEq) (req2: sp1.toFiniteLabel req1 = .finite) (sp2: SequenceProd α β) : IsPrefix sp1 (append sp1 req1 req2 sp2)

namespace IsPrefix

variable {sp1 sp: SequenceProd α β}

theorem of_nil : IsPrefix nil sp := by
  refine IsPrefix.intro ?_ ?_ sp |> Eq.subst ?_
  · rw [append_nil_eq_id]; dsimp
  · exact nil_finiteEq
  · exact nil_finite

theorem refl (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite) : IsPrefix sp sp := by
  refine IsPrefix.intro req1 req2 nil |> Eq.subst ?_
  rw [append_self_nil_eq_self]

theorem getAt?_eq (h: IsPrefix sp1 sp) {i: ℕ} (req: i < sp1.minLength?) : sp1.getAt? i = sp.getAt? i := by
  rcases h with ⟨lm1, lm2, sp2⟩
  symm
  exact append_getAt?_of_lt_length req

theorem getAt?_eq_at (h: IsPrefix sp1 sp) (i: ℕ) (req: i < sp1.minLength?) : sp1.getAt? i = sp.getAt? i := h.getAt?_eq req

end IsPrefix

@[mk_iff]
inductive IsSuffix (sp2: SequenceProd α β) : SequenceProd α β → Prop where
  | intro (sp1: SequenceProd α β) (req1: sp1.toFiniteLabelEq = .labelEq) (req2: sp1.toFiniteLabel req1 = .finite) : IsSuffix sp2 (append sp1 req1 req2 sp2)

namespace IsSuffix

variable {sp: SequenceProd α β}

theorem of_nil (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite) : IsSuffix nil sp := by
  refine IsSuffix.intro sp req1 req2 |> Eq.subst ?_
  rw [append_self_nil_eq_self]


theorem refl : IsSuffix sp sp := by
  refine IsSuffix.intro nil nil_finiteEq nil_finite |> Eq.subst ?_
  rw [append_nil_eq_id]
  dsimp

end IsSuffix

end Nemonuri.SequenceProd

end
