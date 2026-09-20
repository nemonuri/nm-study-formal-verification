module

public import Nemonuri.Functions.RestrictedLeftInverse
public import Nemonuri.Functions.Lifting
public import Nemonuri.Functions.SimpLemmas
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Embedding.Basic


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions


structure LiftableEmbeddingStructure (L R: Type*) where
  embed: L → R
  lift (rv: R) (req: rv ∈ Set.range embed) : L

structure IsLiftableEmbedding {L R: Type*} (s: LiftableEmbeddingStructure L R) : Prop where
  restrictedLeftInverse : RestrictedLeftInverse (· ∈ Set.range s.embed) s.lift s.embed (Set.mem_range_self)

structure LiftableEmbedding (L R: Type*) extends toStruct: LiftableEmbeddingStructure L R where
  valid: IsLiftableEmbedding toStruct

namespace LiftableEmbedding

variable {L R: Type*}


theorem embed_ext {lem1 lem2: LiftableEmbedding L R} (req: lem1.embed = lem2.embed) : lem1 = lem2 := by
  rcases lem1 with ⟨⟨emb1 ,lif1⟩, lm_v1⟩
  rcases lem2 with ⟨⟨emb2, lif2⟩, lm_v2⟩
  simp at ⊢ req
  subst req
  simp [funext_iff]
  intro rv lv lm1
  have lm1_1 := lm1.symm
  subst lm1_1
  revert lm1; simp
  revert lm_v1 lm_v2
  rintro ⟨lm2_1⟩ ⟨lm2_2⟩
  have lm3_1 := lm2_1.eq
  have lm3_2 := lm2_2.eq
  dsimp at lm3_1 lm3_2
  calc
    _ = lv := lm3_1 lv
    _ = _ := (lm3_2 lv).symm


theorem embed_ext_iff {lem1 lem2: LiftableEmbedding L R} : (lem1 = lem2) ↔ (lem1.embed = lem2.embed) :=
  ⟨fun lm1 => congrArg (fun lem => lem.embed) lm1, fun lm1 => embed_ext lm1⟩

theorem embed_injective {lem: LiftableEmbedding L R} : Function.Injective (lem.embed) := lem.valid.restrictedLeftInverse.injective

instance : FunLike (LiftableEmbedding L R) L R where
  coe lem := lem.embed
  coe_injective := by
    intro lem1 lem2 lm1
    dsimp at lm1
    exact embed_ext lm1


theorem coe_injective {lem: LiftableEmbedding L R} : Function.Injective lem := lem.embed_injective

instance : EmbeddingLike (LiftableEmbedding L R) L R where
  injective' lem := lem.coe_injective

def IsLiftable (lem: LiftableEmbedding L R) (rv: R) : Prop := rv ∈ Set.range lem

@[defeq]
theorem isLiftable_def {lem: LiftableEmbedding L R} {rv: R} : IsLiftable lem rv = (rv ∈ Set.range lem) := rfl

@[lift_to_left_norm, range_mem_simp ←]
theorem isLiftable_iff_left_exists {lem: LiftableEmbedding L R} {rv: R} : IsLiftable lem rv ↔ (∃(lv: L), rv = lem lv) := by
  dsimp [isLiftable_def]
  simp only [Set.mem_range]
  exact SimpLemmas.exists_apply_eq_iff

namespace IsLiftable

variable {lem: LiftableEmbedding L R} {rv: R}

theorem left_exists (h: lem.IsLiftable rv) : ∃(lv: L), rv = lem lv := isLiftable_iff_left_exists.mp h

@[lift_to_left_norm]
theorem of_apply {lv: L} : lem.IsLiftable (lem lv) := by simp [isLiftable_def]

theorem intro (lv: L) (req: rv = lem lv) : lem.IsLiftable rv := by
  subst req
  exact of_apply

@[elab_as_elim]
theorem induction
  {motive: lem.IsLiftable rv → Prop}
  (intro: (lv: L) → (req: rv = lem lv) → motive (.intro lv req))
  (t: lem.IsLiftable rv)
  : motive t := by
  obtain ⟨lv, lm1⟩ := t.left_exists
  specialize intro lv lm1
  exact intro

def lift (h: lem.IsLiftable rv) : L := lem.lift rv (isLiftable_def ▸ h)

@[lift_to_left_norm]
theorem lift_eq_self {lv: L} (h: lem.IsLiftable (lem lv)) : h.lift = lv := by
  dsimp [lift]
  exact lem.valid.restrictedLeftInverse.eq lv

@[embed_to_right_norm]
theorem lift_apply_eq_self (h: IsLiftable lem rv) : lem h.lift = rv := by
  obtain ⟨lv, lm1⟩ := h.left_exists
  subst lm1
  simp [lift_to_left_norm]

end IsLiftable

/-
structure Fallback (lem: LiftableEmbedding L R) where
  toFun (rv: R) (req: ¬lem.IsLiftable rv) : L

namespace Fallback

variable {lem: LiftableEmbedding L R}

instance : DFunLike (lem.Fallback) R (fun (rv: R) => (req: ¬lem.IsLiftable rv) → L) where
  coe lfb := lfb.toFun
  coe_injective := by
    rintro ⟨lfb1⟩ ⟨lfb2⟩ lm1
    dsimp at lm1
    subst lm1
    rfl

variable [DecidablePred (lem.IsLiftable ·)]

def liftD (lfb: lem.Fallback) (rv: R) : L := if lm1: lem.IsLiftable rv then lm1.lift else lfb rv lm1

@[lift_to_left_norm]
theorem apply_liftD_eq_self {lfb: lem.Fallback} {lv: L} : lfb.liftD (lem lv) = lv := by
  dsimp [liftD]
  simp [lift_to_left_norm]

theorem liftD_apply_leftInverse {lfb: lem.Fallback} : Function.LeftInverse lfb.liftD lem := by
  intro lv
  exact apply_liftD_eq_self


theorem liftD_surjective {lfb: lem.Fallback} : Function.Surjective (lfb.liftD) := lfb.liftD_apply_leftInverse.surjective

def toLifting (lfb: lem.Fallback) : Lifting R L where
  toFun := lfb.liftD
  surjective := lfb.liftD_surjective


end Fallback
-/

theorem liftable_of_apply (lem: LiftableEmbedding L R) (lv: L) : IsLiftable lem (lem lv) := IsLiftable.of_apply


def comapPi (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) (pir: (rv: R) → mr rv) (lv: L) : mr (lem lv) := pir (lem lv)

def embedPiToRestricted (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) (pi: (lv: L) → mr (lem lv)) (rv: R) (req: lem.IsLiftable rv) : mr rv :=
  have lm1: lem req.lift = rv := req.lift_apply_eq_self
  let x := pi req.lift
  lm1.ndrec x



theorem embedPiToRestricted_eq {lem: LiftableEmbedding L R} {m: R → Sort*} {pi: (lv: L) → m (lem lv)} {lv: L}
  : lem.embedPiToRestricted m pi (lem lv) .of_apply = pi lv := by
  dsimp [embedPiToRestricted]
  symm
  have lm1 := lem.liftable_of_apply lv
  have lm2 := lm1.lift_eq_self
  have lm3 := lm2.symm.rec (motive := fun lv0 lm3_1 => have lm3_2 : lem lv0 = lem lv := congrArg lem lm3_1.symm; (pi lv = lm3_2.ndrec (pi lv0))) rfl
  simpa using lm3

theorem embedPi_injective {l: LiftableEmbedding L R} {m: R → Sort*} : Function.Injective (l.embedPiToRestricted m) := by
  intro pi1 pi2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  have lm2 := l.liftable_of_apply lv
  specialize lm1 (l lv) lm2
  simp [embedPiToRestricted_eq] at lm1
  exact lm1


structure Fallback.{u} (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort u) where
  toFun (rv: R) (req: ¬lem.IsLiftable rv) : mr rv

namespace Fallback

variable {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*}

instance : DFunLike (lem.Fallback mr) R (fun (rv: R) => (req: ¬lem.IsLiftable rv) → (mr rv)) where
  coe lfb := lfb.toFun
  coe_injective := by
    rintro ⟨lfb1⟩ ⟨lfb2⟩ lm1
    dsimp at lm1
    subst lm1
    rfl


variable [DecidablePred (lem.IsLiftable ·)]



def embedPi (lfb: lem.Fallback mr) (pil: (lv: L) → mr (lem lv)) (rv: R) : mr rv :=
  if lm1: lem.IsLiftable rv then
    have lm2: lem lm1.lift = rv := lm1.lift_apply_eq_self
    lm2.ndrec (pil lm1.lift)
  else
    lfb rv lm1

/-
theorem embedPi_injective {lfb: lem.Fallback mr} : Function.Injective (lfb.embedPi) := by
  intro pil1 pil2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  specialize lm1 (lem lv)
  simp [embedPi, lift_to_left_norm] at lm1
-/

/-
theorem liftPi_embedPi_eq {lfb: lem.Fallback mr} {pir: (rv: R) → mr rv} : lfb.embedPi (lem.liftPi mr pir) = pir := by
  simp only [funext_iff]
  intro rv
  dsimp [LiftableEmbedding.liftPi, embedPi]
  by_cases lm1: lem.IsLiftable rv
  · simp [lm1]
    cases lm1 using IsLiftable.induction
    rename_i lv lm1
    have lm1_1 := lm1
    subst lm1_1
    revert lm1; simp
    sorry
  · rcases lfb with ⟨lfb⟩
    simp [lm1]
-/


--def liftPiD (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv)

/-
def liftD (lfb: lem.Fallback mr) (rv: R) : mr rv :=
  if lm1: lem.IsLiftable rv then
    lem lm1.lift
  else
    lfb rv lm1
-/


end Fallback


end LiftableEmbedding

end Nemonuri.Functions

end
