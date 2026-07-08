module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Nemonuri

structure ModelChecking (M: Type*) where
  fintype: Fintype M
  specs: List (M → Prop)
  specToDecidable (spec: M → Prop) (req: spec ∈ specs) : DecidablePred spec


namespace ModelChecking

variable {M: Type*}

--def ToProp (mc: ModelChecking M) : Prop := ∀m ∈ mc.univ, ∀spec ∈ mc.specs, spec m

--@[reducible]
--def check_aux (fintype: Fintype M) (specs: List (M → Prop))

/-
@[reducible]
def check_aux fintype specs decidable : Decidable (ToProp (⟨fintype, specs, decidable⟩: ModelChecking M)) :=
  match specs with
  | [] => .isTrue (by simp [ToProp])
  | hd_spec::tl =>
  let dec1 : Decidable (∀(m: M), hd_spec m) := @fintype.decidableForallFintype _ hd_spec (decidable hd_spec)
  if h2: dec1.decide _ then
    let dec2 : Decidable (ToProp ⟨fintype, specs, inferInstance⟩) := check_aux fintype tl decidable
    --@decidable_of_decidable_of_iff _ _ dec2
-/
--def check (mc: ModelChecking M) : Bool :=


--set_option trace.Debug.Meta.Tactic.simp true
--set_option trace.Meta.Tactic.simp.heads true

def check (mc: ModelChecking M) : Bool :=
  let (eq := h1) ⟨fintype, specs, specToDecidable⟩ := mc
  match h2: specs with
  | [] => .true
  | hd_spec::tl =>
  let dec1 := @fintype.decidableForallFintype M hd_spec (specToDecidable hd_spec (by simp))
  match dec1 with
  | .isFalse _ => .false
  | .isTrue _ =>
    let dec2 spec (req: spec ∈ tl) : DecidablePred spec := fun (m: M) => specToDecidable spec (by simp [req]) m
    ModelChecking.mk fintype tl dec2 |> check


theorem check_iff (mc: ModelChecking M) : (mc.check = .true) ↔ ∀spec ∈ mc.specs, ∀model, spec model := by
  rcases mc with ⟨fintype, specs, specToDecidable⟩
  induction specs with
  | nil =>
    unfold check
    simp only [List.not_mem_nil, false_implies, implies_true]
  | cons hd_spec tl tl_ih =>
    unfold check
    simp
    split
    · simp only [Bool.false_eq_true, false_iff, not_and]
      intro _; contradiction
    · simp only at tl_ih
      rename_i h _
      simp [h]
      rw [← tl_ih]

def myFunc (arr : Array Nat) : Unit := Id.run do
  let mut abc := 0
  if 0 = 0 then
    ()
  for (i, j) in [(0, 0)] do
    let a : Nat := i + 2
    if h : arr.size ≤ 4 then
      continue
    else if h : arr[4] ≤ a then
      continue
    else
      if 0 = 0 then
        continue
      abc := 0

set_option pp.notation false in
#print myFunc

/-
  unfold check
  split
  · grind only [← List.not_mem_nil]
  · rcases mc with ⟨fintype,_,_⟩
    subst_eqs
    extract_lets dec1 dec2
    subst dec1 dec2
    split
    · simp? [-not_forall]
      intro lm1 lm2
      rename_i heq
      revert heq
      simp
      --rename_i heq
      --simp at heq
-/
    --subst dec1
    --revert mc
    --dsimp
    --rename_i mc_eq _ _ _ _ _
    --subst mc_eq
    --split
    --· rename_i mc_eq _ _ _ _ _ _

/-
  if h3: dec1.decide _ then
    sorry
  else
    .false
-/

/-
  match h1: mc.specs with
  | [] => .true
  | hd::tl =>
    have lm1 :
-/

/-
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


instance decidableIsValid (mc: ModelChecking M) : Decidable (IsValid mc) := decidableIsValid_aux mc.fintype mc.specs
-/


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
