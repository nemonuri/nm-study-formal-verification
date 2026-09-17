module

--public meta import Nemonuri.HasHUnion.Attributes
public import Nemonuri.HasHunion.SimpLemmas
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Embedding.Basic


@[expose] public section

set_option autoImplicit false

namespace Nemonuri

theorem LiftableEmbedding.apply_mem {L R: Type*} {emb: L ↪ R} {x: L} : (emb x) ∈ Set.range emb := by simp

open LiftableEmbedding in
structure LiftableEmbedding (L R: Type*) extends toEmbedding: L ↪ R where
  lift (rv: R) (req: rv ∈ Set.range toEmbedding) : L
  lift_valid (lv: L) : lift (toEmbedding lv) (apply_mem) = lv



namespace LiftableEmbedding

variable {L R: Type*}

instance toFunlike : FunLike (LiftableEmbedding L R) L R where
  coe x := (x.toEmbedding: L → R)
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

instance : EmbeddingLike (LiftableEmbedding L R) L R where
  injective' x := x.toEmbedding.injective

@[defeq, lift_to_left_norm ←]
theorem coe_eq_toEmbedding_coe {l: LiftableEmbedding L R} : (l: L → R) = (l.toEmbedding: L → R) := rfl

theorem apply_injective {l: LiftableEmbedding L R} : Function.Injective l := l.toEmbedding.injective

@[range_mem_simp]
theorem toEmbedding_range_mem_iff_exists {l: LiftableEmbedding L R} {rv: R}
  : (rv ∈ Set.range l.toEmbedding) ↔ ∃(lv: L), l.toEmbedding lv = rv := by
  simp only [Set.mem_range]

@[range_mem_simp]
theorem range_mem_iff_exists {l: LiftableEmbedding L R} {rv: R}
  : (rv ∈ Set.range l) ↔ ∃(lv: L), l lv = rv := by
  dsimp [coe_eq_toEmbedding_coe]
  exact toEmbedding_range_mem_iff_exists

theorem apply_lift_eq_self {l: LiftableEmbedding L R} {lv: L} : l.lift (l lv) (apply_mem) = lv := l.lift_valid lv

def IsLiftable (l: LiftableEmbedding L R) (rv: R) : Prop := rv ∈ Set.range l

@[defeq, lift_to_left_norm ←, embed_to_right_norm ←]
theorem IsLiftable_def {l: LiftableEmbedding L R} {rv: R} : IsLiftable l rv = (rv ∈ Set.range l) := rfl

namespace IsLiftable

variable {l: LiftableEmbedding L R} {rv: R}

theorem left_exists (h: IsLiftable l rv) : ∃(lv: L), rv = l lv := by
  dsimp [IsLiftable_def] at h
  simp [range_mem_simp] at h
  exact h

@[lift_to_left_norm, range_mem_simp ←]
theorem left_exists_iff : (∃(lv: L), rv = l lv) ↔ (IsLiftable l rv) := by
  constructor
  · intro lm1
    simp only [IsLiftable_def, range_mem_simp]
    exact lm1
  · exact left_exists

@[lift_to_left_norm]
theorem of_apply {lv: L} : IsLiftable l (l lv) := by simp [IsLiftable_def]

theorem mk (lv: L) (req: rv = l lv) : l.IsLiftable rv := by
  subst req
  exact of_apply

--@[lift_to_left_norm]
theorem of_eq_comp_exists {α: Type*} {f: α → L} (req: ∃(x: α), rv = (l ∘ f) x) : IsLiftable l rv := by
  rcases req with ⟨x, lm1⟩
  subst lm1
  dsimp
  exact of_apply

/-
  constructor
  · exact of_eq_comp_exists
  · simp [range_mem_simp]
    intro lv lm1
    subst lm1
    simp only [EmbeddingLike.apply_eq_iff_eq]
-/


--theorem of_apply_at (l: LiftableEmbedding L R) (lv: L) : IsLiftable l (l lv) := of_apply

def lift (h: IsLiftable l rv) : L := l.lift rv (IsLiftable_def ▸ h)

@[defeq, lift_to_left_norm ←, embed_to_right_norm ←, range_mem_simp]
theorem lift_def {h: IsLiftable l rv} : h.lift = l.lift rv (IsLiftable_def ▸ h) := rfl

@[lift_to_left_norm]
theorem lift_eq_self {lv: L} (h: IsLiftable l (l lv)) : h.lift = lv := by
  dsimp [lift_def]
  exact apply_lift_eq_self

@[lift_to_left_norm]
theorem lift_eq_self_of_eq (h: IsLiftable l rv) {lv: L} (req: rv = l lv) : h.lift = lv := by
  subst req
  exact h.lift_eq_self

@[embed_to_right_norm]
theorem lift_apply_eq_self (h: IsLiftable l rv) : l h.lift = rv := by
  obtain ⟨lv, lm1⟩ := h.left_exists
  subst lm1
  simp [lift_to_left_norm]

theorem eq_comp_exists_iff {α: Type*} {l2: LiftableEmbedding α L}
  : (∃(x: α), rv = (l ∘ l2) x) ↔ (∃(h: IsLiftable l rv), IsLiftable l2 h.lift) := by
  constructor
  · intro lm1
    refine ⟨?_, ?_⟩
    · exact of_eq_comp_exists lm1
    · revert lm1
      simp [range_mem_simp]
      intro x lm1
      subst lm1
      simp [lift_to_left_norm]
  · simp [range_mem_simp]
    intro x lm1 x2 lm2
    subst lm1
    simp [lift_to_left_norm] at lm2
    subst lm2
    simp

@[elab_as_elim]
theorem induction
  {motive: l.IsLiftable rv → Prop}
  (mk: (lv: L) → (req: rv = l lv) → motive (.mk lv req))
  (t: l.IsLiftable rv)
  : motive t := by
  obtain ⟨lv, lm1⟩ := t.left_exists
  specialize mk lv lm1
  exact mk

--theorem apply_eq

end IsLiftable

theorem liftable_of_apply (l: LiftableEmbedding L R) (lv: L) : IsLiftable l (l lv) := IsLiftable.of_apply

namespace IsLiftable

variable {l: LiftableEmbedding L R} {rv: R}

@[lift_to_left_norm]
theorem lift_eq_of_apply_eq {lv: L} (req: rv = l lv) : (req.symm ▸ l.liftable_of_apply lv).lift = lv := by
  subst req
  simp [lift_to_left_norm]

/-
theorem induction₂
  {motive: (rv: R) → (h: l.IsLiftable rv) → Prop}
  (apply: (lv: L) → motive (l.liftable_of_apply lv))
-/


/-
theorem hind.{umr}
  (mr: (rv: R) → Sort umr)
  {motive: (lv: L) → (mr (l lv)) → Prop}
  --(h: (lv: L) → motive lv (mr (l lv)))
  --(lv: L) (t: )
  --(t: mr (l (l.liftable_of_apply)))
-/
end IsLiftable



abbrev DecidableIsLiftable (l: LiftableEmbedding L R) (rv: R) : Type _ := Decidable (l.IsLiftable rv)

namespace DecidableIsLiftable

variable {l: LiftableEmbedding L R} {rv: R}

@[reducible]
def ofApply (lv: L) : l.DecidableIsLiftable (l lv) := Decidable.isTrue .of_apply

@[reducible]
def ofApplyEq {lv: L} (req: l lv = rv) : l.DecidableIsLiftable rv := req.ndrec (ofApply lv)

@[reducible]
def ofIndicator (ind: R → Bool) (req: (ind rv = .true) ↔ (l.IsLiftable rv)) : l.DecidableIsLiftable rv := decidable_of_decidable_of_iff req

end DecidableIsLiftable


def LiftableRight (l: LiftableEmbedding L R) : Type _ := { rv: R // l.IsLiftable rv }

namespace LiftableRight

variable {l: LiftableEmbedding L R}

def mk (rv: R) (req: l.IsLiftable rv) : LiftableRight l := Subtype.mk rv req

@[defeq, embed_to_right_norm ←]
theorem mk_def {rv: R} {req: l.IsLiftable rv} : mk rv req = ⟨rv, req⟩ := rfl

def val (lr: LiftableRight l) : R := Subtype.val lr

@[defeq, simp 10]
theorem mk_val {rv: R} {req: l.IsLiftable rv} : (mk rv req).val = rv := rfl

theorem liftable (lr: LiftableRight l) : l.IsLiftable lr.val := lr.property

@[defeq, simp 10]
theorem mk_liftable {rv: R} {req: l.IsLiftable rv} : (mk rv req).liftable = req := rfl

/-
@[defeq]
protected theorem eta {lr: LiftableRight l} : (mk lr.val lr.liftable) = lr := rfl
-/

--theorem liftable_eta {lr: LiftableRight l} : (mk lr.val lr.liftable).liftable

@[elab_as_elim]
protected def rec.{u}
  {motive: LiftableRight l → Sort u}
  (mk: (rv: R) → (req: l.IsLiftable rv) → motive (LiftableRight.mk rv req))
  (t: LiftableRight l)
  : motive t :=
  mk t.val t.liftable

@[ext]
protected theorem ext {lr1 lr2: LiftableRight l} (req: lr1.val = lr2.val) : lr1 = lr2 := Subtype.ext req

attribute [embed_to_right_norm] LiftableRight.ext_iff

def lift (lr: LiftableRight l) : L := lr.liftable.lift --l.lift lr.val (IsLiftable_def ▸ lr.liftable)

@[defeq, lift_to_left_norm low, embed_to_right_norm low]
theorem lift_def {lr: LiftableRight l} : lr.lift = lr.liftable.lift := rfl

@[defeq]
theorem lift_eq_val_lift {lr: LiftableRight l} : lr.lift = l.lift lr.val (IsLiftable_def ▸ lr.liftable) := by
  dsimp [lift_def, IsLiftable.lift_def]

@[lift_to_left_norm]
theorem lift_eq_of_val_eq {lr: LiftableRight l} {lv: L} (req: lr.val = l lv) : lr.lift = lv := by
  dsimp [lift_def]
  simp [req, lift_to_left_norm]


theorem lift_injective : Function.Injective (lift: LiftableRight l → L) := by
  intro lr1 lr2 lm1
  dsimp [lift_def] at lm1
  have lm3 := lr1.liftable.left_exists
  obtain ⟨lv1, lm2_1⟩ := lr1.liftable.left_exists
  obtain ⟨lv2, lm2_2⟩ := lr2.liftable.left_exists
  simp [lift_to_left_norm, lm2_1, lm2_2] at lm1
  simp [embed_to_right_norm]
  simpa [lm2_1, lm2_2] using lm1

@[lift_to_left_norm ←, embed_to_right_norm]
theorem lift_eq_iff_val_eq {lr1 lr2: LiftableRight l} : (lr1.lift = lr2.lift) ↔ (lr1.val = lr2.val) :=
  calc
    _ ↔ _ := lift_injective.eq_iff
    _ ↔ _ := LiftableRight.ext_iff

--@[embed_to_right_norm]
theorem mk_val_eq_apply {lv: L} : (LiftableRight.mk (l lv) .of_apply).val = l lv := by simp

@[embed_to_right_norm]
theorem lift_apply_eq_val {lr: LiftableRight l} : l lr.lift = lr.val := by
  cases lr using LiftableRight.rec
  simp [embed_to_right_norm]

end LiftableRight

namespace IsLiftable

variable {l: LiftableEmbedding L R} {rv: R}

@[defeq, embed_to_right_norm ←]
theorem lift_eq_liftableRight_mk_lift (h: IsLiftable l rv) : h.lift = (LiftableRight.mk rv h).lift := by
  dsimp [LiftableRight.lift_def]

@[embed_to_right_norm]
theorem liftableRight_mk_lift_apply_eq_self (h: IsLiftable l rv) : l (LiftableRight.mk rv h).lift = rv := by
  simp [embed_to_right_norm]


end IsLiftable





def refl (L: Type*) : LiftableEmbedding L L where
  toEmbedding := Function.Embedding.refl L
  lift rv _ := rv
  lift_valid lv := Function.Embedding.refl_apply _ lv

instance decidableIsLiftableOfRefl (L: Type*) (rv: L) : (refl L).DecidableIsLiftable rv := .isTrue (by simp [range_mem_simp]; exists rv)


def ofInjective (L R: Type*)
  (emb: L → R) (req1: Function.Injective emb)
  (lift: { rv: R // ∃(lv: L), rv = emb lv } → L) (req2: ∀(lv: L), lift ⟨emb lv, Exists.intro _ rfl⟩ = lv)
  : LiftableEmbedding L R :=
  let embedding : L ↪ R := ⟨emb, req1⟩
  {
    toEmbedding := embedding
    lift rv req := lift ⟨rv, (Set.mem_range.trans SimpLemmas.exists_apply_eq_iff).mp req⟩
    lift_valid := by
      subst embedding
      dsimp
      exact req2
  }

@[range_mem_simp (default+1)]
theorem ofInjective_liftable_iff {L R emb req1 lift req2 rv}
  : (ofInjective L R emb req1 lift req2).IsLiftable rv ↔ (∃(lv: L), rv = emb lv) := by
  simp [range_mem_simp]
  dsimp [ofInjective, coe_eq_toEmbedding_coe]
  exact Iff.rfl


def sumLeft (L1 L2: Type*) : LiftableEmbedding L1 (L1 ⊕ L2) :=
  .ofInjective L1 (L1 ⊕ L2) Sum.inl Sum.inl_injective
             (fun rv => match lm1: rv.val with
                        | .inl lv => lv
                        | .inr _ => absurd rv.property (by revert rv; simp))
             (by simp)


instance decidableIsLiftableOfSumLeft (L1 L2: Type*) rv : (sumLeft L1 L2).DecidableIsLiftable rv :=
  .ofIndicator (Sum.isLeft) (by simp [sumLeft, range_mem_simp, Sum.isLeft_iff])



def sumRight (L1 L2: Type*) : LiftableEmbedding L2 (L1 ⊕ L2) :=
  .ofInjective L2 (L1 ⊕ L2) Sum.inr Sum.inr_injective
             (fun rv => match lm1: rv.val with
                        | .inl _ => absurd rv.property (by revert rv; simp)
                        | .inr lv => lv)
             (by simp)


instance decidableIsLiftableOfSumRight (L1 L2: Type*) rv : (sumRight L1 L2).DecidableIsLiftable rv :=
  .ofIndicator (Sum.isRight) (by simp [sumRight, range_mem_simp, Sum.isRight_iff])


namespace LiftableRight


def pure (l: LiftableEmbedding L R) (lv: L) : LiftableRight l := .mk (l lv) .of_apply

variable {l: LiftableEmbedding L R}

@[defeq, embed_to_right_norm ←]
theorem pure_def {lv: L} : LiftableRight.pure l lv = .mk (l lv) .of_apply := rfl

@[embed_to_right_norm ← low]
theorem pure_val_eq_apply {lv: L} : (LiftableRight.pure l lv).val = l lv := by
  rw [← LiftableRight.mk_val_eq_apply]
  dsimp [pure_def]

theorem lift_pure_left_inverse : Function.LeftInverse (LiftableRight.lift) (LiftableRight.pure l) := by
  intro lv
  dsimp [LiftableRight.pure]
  simp [lift_to_left_norm]


theorem pure_injective : Function.Injective (LiftableRight.pure l) := lift_pure_left_inverse.injective

theorem lift_pure_right_inverse : Function.RightInverse (LiftableRight.lift) (LiftableRight.pure l) := by
  intro lr
  dsimp [LiftableRight.pure]
  simp [embed_to_right_norm]

@[simps]
def equivOfPure (l: LiftableEmbedding L R) : L ≃ LiftableRight l where
  toFun lv := LiftableRight.pure l lv
  invFun lrv := lrv.lift
  left_inv := lift_pure_left_inverse
  right_inv := lift_pure_right_inverse


def bind (l: LiftableEmbedding L R) (lr: LiftableRight l) (f: L → LiftableRight l) : LiftableRight l := f lr.lift


end LiftableRight





/-
def lift? (l: LiftableEmbedding L R) (rv: R) (dec: l.DecidableIsLiftable rv) : Option L :=
  if lm1: l.IsLiftable rv then .some (lm1.lift) else .none

def bind? (l: LiftableEmbedding L R) (lr: Option l.LiftableRight) (f: L → Option l.LiftableRight) : Option (l.LiftableRight) :=
  match lr with
  | .none => .none
  | .some lr => f lr.lift
-/


protected def id (L: Type*) : LiftableEmbedding L L := .ofInjective _ _ id Function.injective_id (fun rv => rv.val) (by simp)

section Id

variable {L: Type*} {v: L}

theorem id_liftable : (LiftableEmbedding.id L).IsLiftable v := by simp [LiftableEmbedding.id, range_mem_simp]

instance decidableIsLiftableOfId : (LiftableEmbedding.id L).DecidableIsLiftable v := .isTrue id_liftable

end Id



/-
def compToEmbedding {L R1 R2: Type*} (lhs: LiftableEmbedding R1 R2) (rhs: LiftableEmbedding L R1) : Function.Embedding L R2 :=
  .mk (lhs ∘ rhs) (lhs.apply_injective.comp rhs.apply_injective)
-/
-- lift_to_left_norm embed_to_right_norm

protected def comp {L R1 R2: Type*} (lhs: LiftableEmbedding R1 R2) (rhs: LiftableEmbedding L R1) : LiftableEmbedding L R2 :=
  .ofInjective L R2
    (lhs ∘ rhs) (lhs.apply_injective.comp rhs.apply_injective)
    (fun rv => (IsLiftable.eq_comp_exists_iff.mp rv.property).choose_spec.lift)
    (by intro lv; simp [range_mem_simp]; simp [lift_to_left_norm])


@[defeq]
theorem comp_apply {L R1 R2: Type*} {lhs: LiftableEmbedding R1 R2} {rhs: LiftableEmbedding L R1} {lv: L}
  : (lhs.comp rhs) lv = lhs (rhs lv) :=
  rfl

theorem comp_liftable_iff {L R1 R2: Type*} {lhs: LiftableEmbedding R1 R2} {rhs: LiftableEmbedding L R1} {rv2: R2}
  : ((lhs.comp rhs).IsLiftable rv2) ↔ (∃(h: lhs.IsLiftable rv2), rhs.IsLiftable h.lift) := by
  conv =>
    lhs
    simp [LiftableEmbedding.comp, range_mem_simp]
  exact IsLiftable.eq_comp_exists_iff


def range (l: LiftableEmbedding L R) : Set R := { rv | l.IsLiftable rv }

theorem range_mem_iff {l: LiftableEmbedding L R} {rv: R} : rv ∈ l.range ↔ l.IsLiftable rv := by
  dsimp [range]
  rfl


structure AreLiftable {L1 L2 R: Type*} (l1: LiftableEmbedding L1 R) (l2: LiftableEmbedding L2 R) (rv: R) : Prop where
  fst: l1.IsLiftable rv
  snd: l2.IsLiftable rv

inductive AnyLiftable {L1 L2 R: Type*} (l1: LiftableEmbedding L1 R) (l2: LiftableEmbedding L2 R) (rv: R) : Prop where
  | fst (req: l1.IsLiftable rv)
  | snd (req: l2.IsLiftable rv)

inductive LiftResult (l: LiftableEmbedding L R) where
  | ok (lv: L)
  | error (rv: R) (req: ¬l.IsLiftable rv)

def lift? (l: LiftableEmbedding L R) (rv: R) [l.DecidableIsLiftable rv] : l.LiftResult :=
  if lm1: l.IsLiftable rv then .ok lm1.lift else .error rv lm1

def embedPi (l: LiftableEmbedding L R) (m: R → Sort*) (pi: (lv: L) → m (l lv)) (rv: R) (req: l.IsLiftable rv) : m rv :=
  have lm1: l req.lift = rv := req.lift_apply_eq_self
  let x := pi req.lift
  lm1.ndrec x
  --pi req.lift |> cast (by simp [embed_to_right_norm])


theorem embedPi_eq {l: LiftableEmbedding L R} {m: R → Sort*} {pi: (lv: L) → m (l lv)} {lv: L}
  : l.embedPi m pi (l lv) .of_apply = pi lv := by
  dsimp [embedPi]
  symm
  have lm1 := l.liftable_of_apply lv
  have lm2 := lm1.lift_eq_self
  have lm3 := lm2.symm.rec (motive := fun lv0 lm3_1 => have lm3_2 : l lv0 = l lv := congrArg l lm3_1.symm; (pi lv = lm3_2.ndrec (pi lv0))) rfl
  simpa using lm3


#print embedPi_eq

  --have lm3 := Eq.refl (pi lv)

  --have lm4 (x: m (l lv)) := @lm3.rec
  --have lm1 := (l.liftable_of_apply lv).lift_eq_self.symm
  --symm
  --have lm2 := HEq.refl (pi lv)
  --replace lm1 := heq_of_eq lm1

  --refine' lm1.ndrec lm2
  --have lm3 := @lm1.ndrec

  --have lm2 := HEq.refl lv
  --have lm2 := @dcongr_heq
  --have := heq

/-
  let (eq := lm2) lv2 := lv
  simp only [← lm2] at lm1
  have lm3 := lm1.lift_eq_self
-/
  --generalize lm4: lm
  --let_to_have
  --cases lm1
  --have lm1 := l.liftable_of_apply lv
/-
  let (eq := lm1) ml (lv0: L) : Sort u := m (l lv0)
  simp only [funext_iff] at lm1
  revert pi
  conv => simp [← lm1]
-/

  --conv at pi => ext lv0; simp [← (lm1 lv0)]
  --simp [← lm1] at pi
  --
  --have lm1 := l.liftable_of_apply lv
  --conv => lhs; arg 5; change lm1
/-
  let (eq := lm2) lv2 := lv
  have lm3 : l.IsLiftable (l lv) = l.IsLiftable (l lv2) := by simp [IsLiftable.of_apply]
  dsimp [embedPi]
  rw [lm3]
-/

/-
  dsimp [embedPi]
  have lm2 := lm1.lift_eq_self
  have lm3 := lm1.lift_apply_eq_self
  let (eq := lm4) rv1 := pi lv
  rw [← lm4]
  let (eq := lm5) rv2 := pi lm1.lift
  rw [← lm5]
-/
  --simp [← lm2] at lm3
  --have lm3 := lm1.lift_apply_eq_self



  --dsimp [embedPi]
  --refine' apply_eqRec _
  --have := apply_eqRec
/-
  have lm1 := l.liftable_of_apply lv
  have lm2 := lm1.lift_eq_self
  let (eq := lm3) lv2 := lv
  conv at lm2 => rhs; rewrite [← lm3]
  rw [lm2]
-/

  --extract_lets lm2 lv2
  --have lm3 := lm1.lift_eq_self
  --subst lv2

  --dsimp [Eq.ndrec]

  --conv => ext; simp [lm3]


  --simp [lift_to_left_norm]

/-
theorem embedPi_injective {l: LiftableEmbedding L R} {m: R → Sort*} : Function.Injective (l.embedPi m) := by
  intro pi1 pi2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  have lm2 := l.liftable_of_apply lv
  specialize lm1 (l lv) lm2
  unfold embedPi at lm1
  extract_lets lm3 x1 x2 at lm1
  have lm4 := l.apply_injective.eq_iff.mp lm3
-/

  --cases lm4 using Eq.rec
  --cases lm3 using Eq.rec
  --have := Eq.recOn

  --dsimp [embedPi] at lm1
  --have lm3 : lm2.lift = lv := lm2.lift_eq_self
  --rw [← lm3]

  --exact lm3.subst lm1

  --revert lm1
  --have lm3 : lm2.lift = lv := lm2.lift_eq_self

  --generalize lm2.lift = ddd

/-
  unfold embedPi at lm1
  extract_lets lm3 x1 x2 at lm1
  have lm4 := l.apply_injective.eq_iff.mp lm3
  cases lm2 using IsLiftable.induction
  rename_i lv2 lm2
  have lm5 := l.apply_injective.eq_iff.mp lm2
  conv at lm4 => rhs; rw [lm5]
  subst x1 x2
-/

  --simp [l.apply_injective.eq_iff] at lm1
  --have lm4 := l.apply_injective.eq_iff.mp lm3
  --simp at lm1
  --dsimp only [Eq.ndrec] at lm1
  --
  --simp [lm4] at lm1
  --have lm4 := (eq_rec_inj lm2 x1 x2).mp lm1
  --subst x1 x2
  --have :=
  --rewrite [lm3] at x1
  --dsimp only [embedPi] at lm1
  --specialize lm1 (l )
  --rw [eq_rec_inj] at lm1

  --simp [IsLiftable.lift_eq_self] at lm1_1

  --have lm2 := @l.apply_lift_eq_self _ _ lv
  --rewrite [lm2] at lm1
  --have := cast_h
  --have lm2 : l.IsLiftable (l lv) := .of_apply
  --have lm3 := lm2.lift_eq_self
  --dsimp [IsLiftable.lift] at lm1
  --simp [lm3] at lm1
  --have lm2 :

  --rewrite [IsLiftable.lift_eq_self] at lm1

/-
def embedPi (l: LiftableEmbedding L R) (m: l.LiftResult → Sort*) (pil: (lv: L) → m (.ok lv)) (rv: R) [l.DecidableIsLiftable rv] : m (l.lift? rv) :=
  match lm1: l.lift? rv with
  | .ok lv => pil lv
  | .error rv lm2 =>
-/

/-
def embedPi (l: LiftableEmbedding L R) (βl: L → Sort*) (pi: (lv: L) → βl lv) (rv: R) (req: l.IsLiftable rv) : βl (req.lift) := pi req.lift

theorem embedPi_injective {l: LiftableEmbedding L R} {βl: L → Sort*} : Function.Injective (l.embedPi βl) := by
  intro pi1 pi2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  specialize lm1 (l lv) .of_apply
  dsimp [embedPi] at lm1
  rewrite [IsLiftable.lift_eq_self] at lm1
  exact lm1

def rightMotiveOfLeft (l: LiftableEmbedding L R) (βl: L → Sort*) (rv: R) (req: l.IsLiftable rv) : Sort _ := βl req.lift

def leftMotiveOfRight (l: LiftableEmbedding L R) (βr: (rv: R) → l.IsLiftable rv → Sort*) (lv: L) : Sort _ := βr (l lv) .of_apply

theorem leftMotiveOfRight_rightMotiveOfLeft_left_inverse {l: LiftableEmbedding L R}
  : Function.LeftInverse l.leftMotiveOfRight l.rightMotiveOfLeft := by
  intro ml
  simp only [funext_iff]
  intro lv
  dsimp [rightMotiveOfLeft, leftMotiveOfRight]
  simp [lift_to_left_norm]

inductive IsLiftablePi.{u} {L R: Type*} (l: LiftableEmbedding L R)
                       (βr: (rv: R) → l.IsLiftable rv → Sort u) (pir: (rv: R) → (req: l.IsLiftable rv) → βr rv req) : Prop where
  | intro (βl: L → Sort u)
          (pil: (lv: L) → βl lv) --(req: (lv: L) → pi (l lv) .of_apply = (l.embedPi _ lpi (l lv) .of_apply))
          (req: pir ≍ l.embedPi βl pil)
-/

-- ≍ l.embedPi _ lpi lift_apply_eq_self

--#print IsLiftablePi

namespace IsLiftablePi

variable {l: LiftableEmbedding L R} {βr: (rv: R) → l.IsLiftable rv → Sort*} {pir: (rv: R) → (req: l.IsLiftable rv) → βr rv req}

--set_option pp.proofs true in

/-
theorem of_embedPi {l: LiftableEmbedding L R} {βl: L → Sort*} {pil: (lv: L) → βl lv}
  : IsLiftablePi l (l.rightMotiveOfLeft βl) (l.embedPi _ pil) := by
  refine .intro βl pil ?_
  exact HEq.refl _

def lift (h: IsLiftablePi l βr pir) (lv: L) : l.leftMotiveOfRight βr lv :=
  pir (l lv) .of_apply
-/


--theorem codomain_type_eq {rv: R} {req: l.IsLiftable rv} : βr (l req.lift) .of_apply = βr rv req := by simp [embed_to_right_norm]

--#check eqRec_heq

--set_option pp.explicit true in
/-
theorem sadf___ {lpi: (lv: L) → βr (l lv) .of_apply} --{rv: R} {req: l.IsLiftable rv}
  : (pi ≍ l.embedPi _ lpi) ↔ (∀rv req, pi rv req ≍ (l.embedPi _ lpi rv req)) := by
  have lm1 (rv: R) (req: l.IsLiftable rv) := @codomain_type_eq L R l βr rv req
  constructor
  · intro lm2 rv req
    refine congr_he
-/

      --dsimp [embedPi]


  --have lm1 := @codomain_type_eq L R l βr rv req
/-
  conv =>
    conv =>
      lhs
      arg 2
-/
  --constructor
  --· intro lm1
    --have := heq_fu



end IsLiftablePi


/-
section Comp

variable {L R1 R2: Type*} {lhs: LiftableEmbedding R1 R2} {rhs: LiftableEmbedding L R1} {rv: R2}

theorem comp_liftable_iff : (lhs.comp rhs).IsLiftable rv := by
  simp? [LiftableEmbedding.comp, range_mem_simp]

end Comp
-/


/-
protected def comp (L R1 R2: Type*) (lhs: LiftableEmbedding R1 R2) (rhs: LiftableEmbedding L R1) : LiftableEmbedding L R2 :=
  let emb : L ↪ R2 := Function.Embedding.mk (lhs.toEmbedding ∘ rhs.toEmbedding) (Function.Injective.comp lhs.toEmbedding.injective rhs.toEmbedding.injective)
  {
    toEmbedding := emb
    lift rv2 req :=
      let rv1 : R1 := lhs.lift rv2 (by
        subst emb
        simp at ⊢ req
        obtain ⟨lv, lm1⟩ := req
        exact Exists.intro _ lm1)
      rhs.lift rv1 (by
        subst emb
        subst rv1
        simp at ⊢ req
        obtain ⟨lv, lm1⟩ := req
        rewrite [Eq.comm] at lm1
        subst lm1
        rewrite [lhs.lift_valid]
        exists lv)
    lift_valid := by
      intro lv
      subst emb
      simp [lhs.lift_valid, rhs.lift_valid]
  }
-/



end LiftableEmbedding


end Nemonuri

end
