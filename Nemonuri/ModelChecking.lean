module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Nemonuri

structure ModelChecking (M: Type*) where
  fintype: Fintype M
  specs: List (Σ spec: (M → Prop), DecidablePred spec)

namespace ModelChecking

variable {M: Type*}

def IsValid (mc: ModelChecking M) : Prop := ∀m ∈ mc.fintype.elems, ∀spec ∈ mc.specs, spec.fst m

@[reducible]
def decidableIsValid_aux fintype specs : Decidable (IsValid (⟨fintype, specs⟩: ModelChecking M)) :=
  match specs with
  | [] => .isTrue (by simp [IsValid])
  | hd_spec::tl =>
    let dec1 : Decidable (∀(m: M), hd_spec.fst m) := @fintype.decidableForallFintype _ hd_spec.fst hd_spec.snd
    if h2: dec1.decide _ then
      let dec2 : Decidable (IsValid (⟨fintype, tl⟩)) := decidableIsValid_aux fintype tl
      @decidable_of_decidable_of_iff _ (IsValid (⟨fintype, hd_spec::tl⟩)) dec2 (by
        subst dec2
        simp only [decide_eq_true_eq] at h2
        simp [IsValid, h2]
      )
    else
      .isFalse (by
        simp only [IsValid]
        intro cont
        simp at h2; rcases h2 with ⟨m, m_p⟩
        specialize cont m (fintype.complete _) hd_spec
        refine cont ?_ |> m_p
        simp
      )

set_option pp.proofs true in
#print decidableIsValid_aux._f

instance decidableIsValid (mc: ModelChecking M) : Decidable (IsValid mc) := decidableIsValid_aux mc.fintype mc.specs

set_option pp.explicit true in
#print decidableIsValid

/-
instance decidableIsValid (mc: ModelChecking M) : Decidable (IsValid mc) :=
  match h1: mc.specs with
  | [] => .isTrue (by simp [IsValid, h1])
  | hd_spec::tl =>
  let dec1 : Decidable (∀(m: M), hd_spec.fst m) := @mc.fintype.decidableForallFintype _ hd_spec.fst hd_spec.snd
  if h2: dec1.decide _ then
    let mc2 : ModelChecking M := ⟨mc.fintype, tl⟩
    let dec2 := decidableIsValid mc2
    @decidable_of_decidable_of_iff _ (IsValid mc) dec2 (by
      rcases mc with ⟨fintype, specs⟩
      subst dec2
      simp_all only [decide_eq_true_eq]
      subst h1
      simp [IsValid, h2]
      subst mc2
      rfl
    )
  else
    .isFalse (by
      simp only [IsValid]
      intro cont
      simp at h2; rcases h2 with ⟨m, m_p⟩
      specialize cont m (mc.fintype.complete _) hd_spec
      refine cont ?_ |> m_p
      simp [h1]
    )
  termination_by mc.specs.length
  decreasing_by
    · simp [h1]
    · subst mc2; simp at h1; subst h1; simp
-/






end ModelChecking



end Nemonuri

end
