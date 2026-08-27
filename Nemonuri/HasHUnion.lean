module

public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Embedding.Basic

@[expose] public section

namespace Nemonuri

theorem LiftableEmbedding.apply_mem {T1 T2: Type*} {emb: T1 ↪ T2} {x: T1} : (emb x) ∈ Set.range emb := by simp

open LiftableEmbedding in
structure LiftableEmbedding (T1 T2: Type*) extends toEmbedding: T1 ↪ T2 where
  lift (t2: T2) (req: t2 ∈ Set.range toEmbedding) : T1
  lift_valid (t1: T1) : lift (toEmbedding t1) (apply_mem) = t1

namespace LiftableEmbedding

variable {T1 T2: Type*}

instance toFunlike : FunLike (LiftableEmbedding T1 T2) T1 T2 where
  coe x := (x.toEmbedding: T1 → T2)
  coe_injective := by
    rintro ⟨emb, lift1, lm1⟩ ⟨emb2, lift2, lm2⟩
    simp
    intro lm3
    subst lm3
    simp [funext_iff]
    intro t2 t1 lm3
    have lm4 := lm3.symm
    subst lm4
    revert lm3; simp
    specialize lm1 t1
    specialize lm2 t1
    rw [lm1, lm2]

instance : EmbeddingLike (LiftableEmbedding T1 T2) T1 T2 where
  injective' x := x.toEmbedding.injective

structure PartialLift (x: LiftableEmbedding T1 T2) where
  partialLift (t2: T2) : Option T1
  partialLift_valid (t2: T2) (t1: T1) : (partialLift t2 = some t1) ↔ (∃req, x.lift t2 req = t1)

end LiftableEmbedding


class HasHUnion.{u1, u2} (T1 T2: Type u1) (T3: outParam <| Type u2) where
  fst: LiftableEmbedding.{u1, u2} T1 T3
  snd: LiftableEmbedding.{u1, u2} T2 T3

namespace HasHUnion

inductive Label where
  | fst
  | snd
  deriving DecidableEq

universe u1 u2

class HasPartialLift (T1 T2: Type u1) (T3: Type u2) [HasHUnion T1 T2 T3] where
  fst: LiftableEmbedding.PartialLift (@HasHUnion.fst T1 T2 T3 _)
  snd: LiftableEmbedding.PartialLift (@HasHUnion.snd T1 T2 T3 _)

section TypeAbbrev

variable (T1 T2: Type u1) (T3: Type u2)

abbrev LeftTypeAt [HasHUnion T1 T2 T3] (lb: Label) : Type u1 :=
  Label.casesOn lb T1 T2

abbrev LiftableEmbeddingTypeAt [HasHUnion T1 T2 T3] (lb: Label) : Type (max u1 u2) := LiftableEmbedding.{u1, u2} (LeftTypeAt T1 T2 T3 lb) T3

def toLiftableEmbeddingAt [HasHUnion T1 T2 T3] (lb: Label) : LiftableEmbeddingTypeAt T1 T2 T3 lb :=
  Label.casesOn lb (HasHUnion.fst T2) (HasHUnion.snd T1)

end TypeAbbrev

/-
variable {T1 T2: Type u1} {T3: Type u2}

instance (priority := low) [HasHUnion T1 T2 T3] : HasHUnion T2 T1 T3 where
  fst := HasHUnion.snd T1
  snd := HasHUnion.fst T2

instance (priority := low) [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] : HasPartialLift T2 T1 T3 where
  fst := HasPartialLift.snd
  snd := HasPartialLift.fst
-/

section ExplicitLeftType

variable (T1 T2: Type u1) {T3: Type u2}

def embedAt [HasHUnion T1 T2 T3] (lb: Label) (lv: LeftTypeAt T1 T2 T3 lb) : T3 := (toLiftableEmbeddingAt T1 T2 T3 lb) lv

theorem embedAt_injective [HasHUnion T1 T2 T3] {lb: Label} : Function.Injective (embedAt T1 T2 lb) := by
  intro x1 x2 lm1
  dsimp [LeftTypeAt] at x1 x2
  dsimp [embedAt, toLiftableEmbeddingAt] at lm1
  cases lb <;> (
    dsimp at x1 x2 lm1
    exact (Function.Embedding.injective _).eq_iff.mp lm1 )

def EmbedRangeAt [HasHUnion T1 T2 T3] (lb: Label) : Set T3 := Set.range (embedAt T1 T2 lb)

def liftAt [HasHUnion T1 T2 T3] (rv: T3) (lb: Label) (req: rv ∈ EmbedRangeAt T1 T2 lb) : LeftTypeAt T1 T2 T3 lb :=
  (toLiftableEmbeddingAt T1 T2 T3 lb).lift rv req


theorem embedAt_liftAt_eq [HasHUnion T1 T2 T3] {lb: Label} {lv: LeftTypeAt T1 T2 T3 lb}
  : liftAt T1 T2 (embedAt T1 T2 lb lv) lb (Set.mem_range_self _) = lv :=
  (toLiftableEmbeddingAt T1 T2 T3 lb).lift_valid lv

end ExplicitLeftType

/-
theorem embedAt_eq_iff [HasHUnion T1 T2 T3] {t1: T1} {t2: T2} : (embedAt T2 T3 t1) = (embedAt T1 T3 t2) := by
  dsimp [embedAt]
  dsimp only [DFunLike.coe]
-/

/-
def liftAt? (T2: Type*) {T3 T1: Type*} [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] (t3: T3) : Option T1 :=
  (@HasPartialLift.fst T1 T2 T3 _ _).partialLift t3


theorem liftAt?_eq_some_iff [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] {t3: T3} {t1: T1}
  : (liftAt? T2 t3 = .some t1) ↔ (∃req, liftAt T2 t3 req = t1) :=
  (@HasPartialLift.fst T1 T2 T3 _ _).partialLift_valid t3 t1


theorem liftAt?_eq_none_iff [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] {t3: T3}
  : (liftAt? T2 t3 = (.none: Option T1)) ↔ (t3 ∉ Set.range (embedAt T2 T3: T1 → T3)) := by
  rw [Option.eq_none_iff_forall_ne_some]
  dsimp
  conv =>
    lhs
    ext
    arg 1
    rw [liftAt?_eq_some_iff]
  simp
  constructor
  · intro lm1 x lm2
    replace lm2 := lm2.symm
    subst lm2
    exact lm1 x x rfl embedAt_liftAt_eq
  · intro lm1 x1 x2 lm2 lm3
    exact lm1 x2 lm2
-/



/-
theorem liftAt?_exists_eq_some_iff [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] {t3: T3}
  : (∃(t1: T1), liftAt? T2 t3 = .some t1) ↔ (t3 ∈ Set.range (embedAt T2 T3: T1 → T3)) := by
  simp [liftAt?, embedAt]
  have lm1 := (@HasPartialLift.fst T1 T2 T3 _ _).partialLift_valid t3
  simp at lm1
  refine Iff.trans ?_ lm1
  exact Option.isSome_iff_exists.symm
-/

/-
theorem embedAt_range_mem_of_liftAt?_eq_some [HasHUnion T1 T2 T3] [HasPartialLift T1 T2 T3] {t3: T3} {t1: T1} (req: liftAt? T2 t3 = .some t1)
  : t3 ∈ Set.range (embedAt T2 T3: T1 → T3) :=
  --liftAt?_exists_eq_some_iff.mp (Exists.intro t1 req)
-/


variable {T1 T2: Type u1} {T3: Type u2} [HasHUnion T1 T2 T3]

def hunionSet (s1: Set T1) (s2: Set T2) : Set T3 := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))

def hunionFinset [DecidableEq T3] (s1: Finset T1) (s2: Finset T2) : Finset T3 := (s1.image (embedAt T1 T2 .fst)) ∪ (s2.image (embedAt T1 T2 .snd))

def hunionIndicator [∀lb rv, Decidable (rv ∈ EmbedRangeAt T1 T2 lb)] (s1: T1 → Bool) (s2: T2 → Bool) (rv: T3) : Bool :=
  let loc2 (_: Unit) : Bool :=
    if lm2: decide (rv ∈ EmbedRangeAt T1 T2 .snd) then
      s2 (liftAt T1 T2 rv .snd (decide_eq_true_iff.mp lm2))
    else
      .false
  if lm1: decide (rv ∈ EmbedRangeAt T1 T2 .fst) then
    if s1 (liftAt T1 T2 rv .fst (decide_eq_true_iff.mp lm1)) then
      .true
    else
      loc2 ()
  else
    loc2 ()


theorem hunionIndicator_eq_true_iff [∀lb rv, Decidable (rv ∈ EmbedRangeAt T1 T2 lb)] {s1: T1 → Bool} {s2: T2 → Bool} {rv: T3}
  : (hunionIndicator s1 s2 rv = .true) ↔ ((∃req1, s1 (liftAt T1 T2 rv .fst req1) = .true) ∨ (∃req2, s2 (liftAt T1 T2 rv .snd req2) = .true)) := by
  cases lm1: decide (rv ∈ EmbedRangeAt T1 T2 .fst)
  <;> cases lm2: decide (rv ∈ EmbedRangeAt T1 T2 .snd)
  <;> (simp at lm1 lm2; simp [lm1, lm2, hunionIndicator])

#print hunionIndicator_eq_true_iff

/-
  revert lm1 lm2
  simp [EmbedRangeAt, LeftTypeAt]
  intro lv1 lm1 lv2 lm2
  constructor
  · rintro ⟨lm3, lm4⟩
    exact Or.inl lm3
  · intro lm3
    rcases lm3 with lm3 | lm3
    <;> simp [lm3]
-/
  --simp [EmbedRangeAt] at lm1 lm2
/-
  · intro lm1
    dsimp [hunionIndicator] at lm1
    split at lm1 <;> (rename_i lm2)
    · revert lm2; simp
      intro lm2 lm1
      refine Or.inl ?_
      exists lm2
    · revert lm2; simp
      simp at lm1
      rcases lm1 with ⟨lm1_1, lm1_2⟩
      intro lm2
      refine Or.inr ?_
      exists lm1_1
  · intro lm1
    rcases lm1 with lm1 | lm1
    <;> (rcases lm1 with ⟨lm1_1, lm1_2⟩)
    · dsimp [hunionIndicator]
      simp [lm1_1]
      exact lm1_2
    · dsimp [hunionIndicator]
      simp
      split <;> rename_i lm2
      · revert lm1_1 lm2
        simp [EmbedRangeAt, LeftTypeAt]
        intro lv2 lm1 lm2 lv1 lm3
        have lm4 :=
-/


/-
  refine not_iff_not.mp ?_
  simp
  constructor
  · intro lm1
    simp [hunionIndicator] at lm1
-/

/-
  Bool.casesOn (motive := fun _ => Bool)
    (decide (rv ∈ EmbedRangeAt T1 T2 .fst))
    (Bool.casesOn (motive := fun _ => Bool)
      (decide (rv ∈ EmbedRangeAt T1 T2 .snd))
      (.false)
      )
-/

/-
def hunionIndicator [HasPartialLift T1 T2 T3] (s1: T1 → Bool) (s2: T2 → Bool) (x: T3) : Bool :=
  match liftAt? T2 x with
  | .some t1 => s1 t1
  | .none =>
  match liftAt? T1 x with
  | .some t2 => s2 t2
  | .none => .false
-/

/-
theorem hunionIndicator_eq_true_iff [HasPartialLift T1 T2 T3] {s1: T1 → Bool} {s2: T2 → Bool} {t3: T3}
  : (hunionIndicator s1 s2 t3 = .true) ↔ ((∃req1, ∃(t1: T1), liftAt T2 t3 req1 = t1 ∧ (s1 t1 = .true) ) ∨ (∃req2, ∃(t2: T2), liftAt T1 t3 req2 = t2 ∧ (s2 t2 = .true))) := by
  constructor
  · intro lm1
    dsimp [hunionIndicator] at lm1
    split at lm1
    · rename_i t1_2 lm2
      refine Or.inl ?_
      rewrite [liftAt?_eq_some_iff] at lm2
      rcases lm2 with ⟨lm2_1, lm2_2⟩
      exists lm2_1
      exists t1_2
    · split at lm1 <;> try simp at lm1
      rename_i t1_2 lm2
      refine Or.inr ?_
      rewrite [liftAt?_eq_some_iff] at lm2
      rcases lm2 with ⟨lm2_1, lm2_2⟩
      exists lm2_1
      exists t1_2
  · intro lm1
    rcases lm1 with lm1 | lm1
    <;> (
      rcases lm1 with ⟨lm1, t1, lm2, lm3⟩
      revert lm1
      simp
      intro x lm1 lm2
      replace lm1_1 := lm1.symm
      subst lm1_1
      rewrite [embedAt_liftAt_eq] at lm2
      subst lm2
      clear lm1 )
    · dsimp [hunionIndicator]
      split <;> (rename_i lm2)
      · rewrite [liftAt?_eq_some_iff] at lm2
        rcases lm2 with ⟨lm2_1, lm2_2⟩
        rewrite [embedAt_liftAt_eq] at lm2_2
        subst lm2_2
        exact lm3
      · rewrite [liftAt?_eq_none_iff] at lm2
        simp at lm2
    · dsimp [hunionIndicator]
      split <;> (rename_i lm2)
      · rename_i t2
        rewrite [liftAt?_eq_some_iff] at lm2
        rcases lm2 with ⟨lm2_1, lm2_2⟩
        revert lm2_1
        simp
        intro t2_1 lm2_1 lm2_2
        simp only [← lm2_1] at lm2_2
        rewrite [embedAt_liftAt_eq] at lm2_2
        subst lm2_2
-/
/-
        split
        · rename_i t2 lm4
          rewrite [liftAt?_eq_some_iff] at lm4
          rcases lm4 with ⟨lm4_1, lm4_2⟩
          revert lm4_1
          simp
          intro t2_1 lm4_1 lm4_2
          rewrite [liftAt?_eq_none_iff] at lm2
-/

    --· dsimp [hunionIndicator]
    --  split

      --dsimp [hunionIndicator]
      --simp at
/-
      split
      · rename_i t1_2 lm3
        rewrite [liftAt?_eq_some_iff] at lm3
        rcases lm3 with ⟨lm3_1, lm3_2⟩
        simp at lm1
-/

/-
theorem hunionIndicator_eq_true [HasPartialLift T1 T2 T3] {s1: T1 → Bool} {s2: T2 → Bool}
  : ({ t3 | hunionIndicator s1 s2 t3 = .true }: Set T3) = (hunionSet { t1 | s1 t1 = .true } { t2 | s2 t2 = .true }) := by
  simp [hunionSet, Set.ext_iff]
  intro t3
  constructor
  · intro lm1
    dsimp [hunionIndicator] at lm1
    split at lm1
    · rename_i t1_2 lm2
      refine Or.inl ?_
      exists t1_2
      simp [lm1]
      replace lm2 := embedAt_range_mem_of_liftAt?_eq_some lm2 |> Set.mem_range.mp
      obtain ⟨t1_3, lm2⟩ := lm2
-/

end HasHUnion


end Nemonuri

end
