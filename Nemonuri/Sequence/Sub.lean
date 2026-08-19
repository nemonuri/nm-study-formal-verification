module

public import Nemonuri.Sequence.Operations

@[expose] public section


namespace Nemonuri.Sequence

variable {α: Type _}

inductive IsPrefix (seq1: Sequence α) : Sequence α → Prop where
  | intro (req: seq1.toFiniteLabel = .finite) (seq2: Sequence α) : IsPrefix seq1 (Sequence.append seq1 req seq2)

namespace IsPrefix

variable {seq1 seq: Sequence α}

theorem iff_exists : IsPrefix seq1 seq ↔ ∃(req: seq1.toFiniteLabel = .finite), ∃(seq2: Sequence α), (Sequence.append seq1 req seq2) = seq := by
  constructor
  · intro lm1
    rcases lm1 with ⟨lm1, seq2⟩
    exists lm1
    exists seq2
  · rintro ⟨lm1, seq2, lm2⟩
    have lm3 := IsPrefix.intro lm1 seq2
    rewrite [lm2] at lm3
    exact lm3


theorem of_nil : IsPrefix nil seq := by
  rw [iff_exists]
  refine Exists.intro ?_ ?_
  · exact Sequence.nil_empty |> finite_of_empty
  · exists seq
    rw [Sequence.append_nil_eq_id]
    dsimp

theorem refl (req: seq.toFiniteLabel = .finite) : IsPrefix seq seq := by
  refine IsPrefix.intro req nil |> Eq.subst ?_
  exact seq.append_self_nil_eq_self req

theorem getAt?_eq (h: IsPrefix seq1 seq) {i: ℕ} (req: i < seq1.length?) : seq.getAt? i = seq1.getAt? i := by
  rcases h with ⟨lm1, seq2⟩
  refine append_getAt?_of_lt_length ?_
  rw [← ENat.coe_lt_coe, ← length?_eq_natCast_length]
  exact req

end IsPrefix


inductive IsSuffix (seq2: Sequence α) : Sequence α → Prop where
  | intro (seq1: Sequence α) (req: seq1.toFiniteLabel = .finite) : IsSuffix seq2 (Sequence.append seq1 req seq2)

namespace IsSuffix

variable {seq2 seq: Sequence α}

theorem iff_exists : IsSuffix seq2 seq ↔ ∃(seq1: Sequence α), ∃(req: seq1.toFiniteLabel = .finite), (Sequence.append seq1 req seq2) = seq := by
  constructor
  · intro lm1
    rcases lm1 with ⟨seq1, req⟩
    exists seq1
    exists req
  · rintro ⟨seq1, lm1, lm2⟩
    refine IsSuffix.intro seq1 lm1 |> Eq.subst ?_
    exact lm2


theorem of_nil (req: seq.toFiniteLabel = .finite) : IsSuffix nil seq := by
  refine IsSuffix.intro seq req |> Eq.subst ?_
  exact seq.append_self_nil_eq_self req

theorem refl : IsSuffix seq seq := by
  refine IsSuffix.intro nil ?_ |> Eq.subst ?_
  · rw [append_nil_eq_id]
    dsimp
  · exact nil_empty |> finite_of_empty


end IsSuffix


end Nemonuri.Sequence

end
