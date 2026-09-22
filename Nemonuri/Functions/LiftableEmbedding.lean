module

public import Nemonuri.Functions.RestrictedLeftInverse
public import Nemonuri.Functions.Lifting
public import Nemonuri.Functions.SimpLemmas
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Fold


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

@[defeq]
theorem comapPi_eq {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} {pir: (rv: R) → mr rv} {lv: L}
  : lem.comapPi mr pir lv = pir (lem lv) := by
  dsimp [comapPi]

/-
theorem comapPi_injective {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} : Function.Injective (lem.comapPi mr) := by
  intro pir1 pir2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro rv
  dsimp [comapPi] at lm1
-/

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

theorem embedPiToRestricted_injective {l: LiftableEmbedding L R} {m: R → Sort*} : Function.Injective (l.embedPiToRestricted m) := by
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

def mergeToPi (lfb: lem.Fallback mr) (pir: (rv: R) → (req: lem.IsLiftable rv) → mr rv) : (rv: R) → mr rv :=
  (RestrictedProd.mk pir lfb).toPi


theorem mergeToPi_injective {lfb: lem.Fallback mr} : Function.Injective (lfb.mergeToPi) := by
  intro pir1 pir2 lm1
  dsimp [mergeToPi] at lm1
  have lm2 := (RestrictedProd.equivOfToPi R (lem.IsLiftable ·) mr).left_inv.injective
  simp [RestrictedProd.equivOfToPi] at lm2
  rewrite [lm2.eq_iff] at lm1
  simp at lm1
  exact lm1


def embedPi (lfb: lem.Fallback mr) (pil: (lv: L) → mr (lem lv)) : (rv: R) → mr rv :=
  lfb.mergeToPi (lem.embedPiToRestricted mr pil)

theorem embedPi_injective (lfb: lem.Fallback mr) : Function.Injective (lfb.embedPi) := by
  intro pil1 pil2 lm1
  dsimp [embedPi] at lm1
  rewrite [mergeToPi_injective.eq_iff] at lm1
  rewrite [embedPiToRestricted_injective.eq_iff] at lm1
  exact lm1


theorem embedPi_eq {lfb: lem.Fallback mr} {pil: (lv: L) → mr (lem lv)} {lv: L}
  : lfb.embedPi pil (lem lv) = pil lv := by
  dsimp [embedPi, mergeToPi, RestrictedProd.toPi]
  have lm1 := lem.liftable_of_apply lv
  simp [lm1]
  exact lem.embedPiToRestricted_eq


theorem embedPi_comapPi_eq {lfb: lem.Fallback mr} {pil: (lv: L) → mr (lem lv)} --{rv: R}
  : lem.comapPi mr (lfb.embedPi pil) = pil := by
  simp only [funext_iff]
  intro lv
  dsimp [comapPi]
  exact lfb.embedPi_eq


theorem comapPi_embedPi_leftInverse {lfb: lem.Fallback mr} : Function.LeftInverse (lem.comapPi mr) lfb.embedPi := by
  intro pil
  exact embedPi_comapPi_eq



variable {mr: (rv: R) → Type*}

def toLiftableEmbedding (lfb: lem.Fallback mr) : LiftableEmbedding ((lv: L) → mr (lem lv)) ((rv: R) → mr rv) where
  embed pil := lfb.embedPi pil
  lift pir _ := lem.comapPi mr pir
  valid := by
    refine .mk ?_
    dsimp [RestrictedLeftInverse]
    intro pil
    exact lfb.embedPi_comapPi_eq

def IsLiftablePi (lfb: lem.Fallback mr) (pi: (rv: R) → mr rv) : Prop := lfb.toLiftableEmbedding.IsLiftable pi

@[defeq]
theorem isLiftablePi_def {lfb: lem.Fallback mr} {pi: (rv: R) → mr rv} : lfb.IsLiftablePi pi = lfb.toLiftableEmbedding.IsLiftable pi := rfl

section

variable {lfb: lem.Fallback mr} {pir: (rv: R) → mr rv}

namespace IsLiftablePi


theorem eq_fallback (h: lfb.IsLiftablePi pir) (rv: R) (req: ¬lem.IsLiftable rv)
  : pir rv = lfb rv req := by
  dsimp [isLiftablePi_def] at h
  cases h using IsLiftable.induction
  rename_i pil lm2
  subst lm2
  conv => lhs; dsimp only [DFunLike.coe, toLiftableEmbedding]
  simp [embedPi, mergeToPi, RestrictedProd.toPi, req]

end IsLiftablePi


theorem isLiftablePi_iff : (lfb.IsLiftablePi pir) ↔ ((rv: R) → (req: ¬lem.IsLiftable rv) → pir rv = lfb rv req) := by
  constructor
  · intro h; exact h.eq_fallback
  · intro lm1
    simp [isLiftablePi_def, isLiftable_iff_left_exists]
    exists (lem.comapPi mr pir)
    conv => rhs; dsimp only [DFunLike.coe, toLiftableEmbedding]
    simp only [funext_iff]
    intro rv
    specialize lm1 rv
    by_cases lm2: lem.IsLiftable rv
    · cases lm2 using IsLiftable.induction
      rename_i lv lm2
      subst lm2
      rw [embedPi_eq, comapPi_eq]
    · specialize lm1 lm2
      refine Eq.trans lm1 ?_
      conv =>
        rhs
        dsimp [embedPi, mergeToPi, RestrictedProd.toPi]
        simp [lm2]


namespace IsLiftablePi

theorem mk (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) (req1: (rv: R) → (req: ¬lem.IsLiftable rv) → pir rv = lfb rv req) : lfb.IsLiftablePi pir :=
  lfb.isLiftablePi_iff.mpr req1

end IsLiftablePi

def decideIsLiftableOfFinset [(rv: R) → DecidableEq (mr rv)] (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) (rs: Finset R) : Bool :=
  rs.fold Bool.and .true (fun rv => if lm1: lem.IsLiftable rv then .true else decide (pir rv = lfb rv lm1))

def decideIsLiftable [Fintype R] [(rv: R) → DecidableEq (mr rv)] (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) : Bool := lfb.decideIsLiftableOfFinset pir Finset.univ

theorem decideIsLiftableOfFinset_eq_true_iff [(rv: R) → DecidableEq (mr rv)] (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) (rs: Finset R)
  : (lfb.decideIsLiftableOfFinset pir rs = .true) ↔ ((rv: rs) → (req: ¬lem.IsLiftable rv.val) → pir rv.val = lfb rv.val req) := by
  cases rs using Finset.cons_induction
  · simp [decideIsLiftableOfFinset]
  · rename_i rv rs lm1 lm2
    clear lm2
    have lm3 := lfb.decideIsLiftableOfFinset_eq_true_iff pir rs
    simp [decideIsLiftableOfFinset] at ⊢ lm3
    intro lm4
    exact lm3
  termination_by rs.card


theorem decideIsLiftable_eq_true_iff_isLiftablePi [(rv: R) → DecidableEq (mr rv)] [Fintype R] (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv)
  : (lfb.decideIsLiftable pir = .true) ↔ lfb.IsLiftablePi pir := by
  rw [lfb.isLiftablePi_iff]
  have lm1 := lfb.decideIsLiftableOfFinset_eq_true_iff pir Finset.univ
  simp at lm1
  dsimp [decideIsLiftable]
  exact lm1


/-
def decideIsLiftable [Fintype R] [(rv: R) → DecidableEq (mr rv)] (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) : Bool :=
  let fsu : Finset R := Finset.univ
  fsu.fold (Bool.and) .true (fun rv => if lm1: lem.IsLiftable rv then .true else decide (pir rv = lfb rv lm1) )
-/
  --let fs := fsu.filter (¬lem.IsLiftable ·) |>.attach
  --fs.fold (Bool.and) .true (fun ⟨rv0, lm1⟩ => decide (pir rv0 = lfb rv0 (by subst fsu; simpa using lm1)))



/-
theorem isLiftablePi_of_decideIsLiftable_eq_true [Fintype R] [(rv: R) → DecidableEq (mr rv)]
  (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) (req: lfb.decideIsLiftable pir = .true)
  : lfb.IsLiftablePi pir := by
  rw [isLiftablePi_iff]
  intro rv lm1
  dsimp [decideIsLiftable] at req
  generalize lm2: (Finset.univ: Finset R) = fsu at req
  have lm3 : rv ∈ fsu := by simp [← lm2]
  let _ : DecidableEq R := Classical.decEq R
  cases fsu using Finset.induction
  · simp at lm3
  · rename_i rv1 fs1 lm4 lm5
    simp at lm3 lm5; clear lm5
    rcases lm3 with lm3 | lm3
    · subst lm3
      simp at req
      rcases req with ⟨lm6, lm7⟩
      exact lm6 lm1
    · simp at req
-/

    --simp at req
/-
  unfold decideIsLiftable at req
  extract_lets fsu fs at req
  subst fs
  dsimp at req
  let deqR : DecidableEq R := Classical.decEq R
  induction lm2: fsu using Finset.induction
  · simp [lm2] at req
-/
/-


  dsimp [decideIsLiftable] at req

  induction lm2: (Finset.univ: Finset R) using Finset.induction
  · simp [lm2] at req
-/
  --dsimp [Finset.fold] at req
  --have := Finset.fold_congr
  --have := Multiset.attach
/-
#print Fintype.induction_subsingleton_or_nontrivial

theorem decideIsLiftable_eq_true_iff_isLiftablePi [Fintype R] [(rv: R) → DecidableEq (mr rv)]
  : (lfb.decideIsLiftable pir = .true) ↔ lfb.IsLiftablePi pir := by
-/
  --simp [decideIsLiftable]
  --induction R using Fintype.induction_subsingleton_or_nontrivial



  --simp [decideIsLiftable]
  --have := Finset.univ_filt
  --simp [Finset.filter_attach']
  --simp [Finset.filter_attach]
  --have :=
  --unfold decideIsLiftable
  --simp [isLiftablePi_iff]
/-
  constructor
  · intro lm1 rv lm2
    rewrite [Finset.fold_op_distrib] at lm1
-/
/-
    induction lm3: fs using Finset.cons_induction
    · subst fs
      simp at lm3
      specialize @lm3 rv
      contradiction
    · rename_i fse fs2 lm4 lm5
      simp [lm3] at lm1
-/
      --rcases fse with ⟨fse, lm6⟩
      --dsimp at lm1 lm3
      --subst fs
/-
    · rename_i fs1 fs1e fs2 fs2e lm4
      by_cases lm5: fs = fs2
      · exact lm4 lm5
      · clear lm4
-/
        --subst fs
        --simp at lm1 lm3 lm5
/-
  constructor
  · intro lm1
    dsimp [decideIsLiftable] at lm1
-/



end




/-
def liftPi (lfb: lem.Fallback mr) (pir: (rv: R) → mr rv) (_: ∃(pil: (lv: L) → (mr (lem lv))), lfb.embedPi pil = pir) : (lv: L) → (mr (lem lv)) :=
  lem.comapPi mr pir
-/


/-
  if lm1: lem.IsLiftable rv then
    have lm2: lem lm1.lift = rv := lm1.lift_apply_eq_self
    lm2.ndrec (pil lm1.lift)
  else
    lfb rv lm1
-/

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
