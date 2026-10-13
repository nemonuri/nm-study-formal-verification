module

public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous


structure EquivStruct (αl αr: Sort*) where
  toFun: αl → αr
  invFun: αr → αl


namespace EquivStruct

variable {αl αr αr2: Sort*} --{βl βr: Sort*}

protected def symm (es: EquivStruct αl αr) : EquivStruct αr αl where
  toFun := es.invFun
  invFun := es.toFun

@[defeq]
theorem symm_symm {es: EquivStruct αl αr} : es.symm.symm = es := by
  dsimp [EquivStruct.symm]



protected def trans (es: EquivStruct αl αr) (es2: EquivStruct αr αr2) : EquivStruct αl αr2 where
  toFun := es2.toFun ∘ es.toFun
  invFun := es.invFun ∘ es2.invFun

structure AreCongruence (es: EquivStruct αl αr) (l: αl) (r: αr) : Prop where
  eq_right: es.toFun l = r
  eq_left: es.invFun r = l

theorem areCongruence_iff_eq {es: EquivStruct αl αr} {l: αl} {r: αr} : es.AreCongruence l r ↔ (r = es.toFun l ∧ l = es.invFun r) := by
  constructor
  · rintro ⟨lm1, lm2⟩
    exact ⟨lm1.symm, lm2.symm⟩
  · rintro ⟨lm1, lm2⟩
    exact ⟨lm1.symm, lm2.symm⟩


namespace AreCongruence

--variable {es: EquivStruct αl αr}

theorem left_unique {es: EquivStruct αl αr} : Relator.LeftUnique (es.AreCongruence) := by
  rintro l1 l2 r ⟨lm1, lm2⟩ ⟨lm3, lm4⟩
  calc
    l1 = _ := lm2.symm
    _ = l2 := lm4

theorem left_unique_at (es: EquivStruct αl αr) (l1 l2: αl) (r: αr) (h1: es.AreCongruence l1 r) (h2: es.AreCongruence l2 r) : l1 = l2 := left_unique h1 h2

theorem right_unique {es: EquivStruct αl αr} : Relator.RightUnique (es.AreCongruence) := by
  rintro l1 l2 r ⟨lm1, lm2⟩ ⟨lm3, lm4⟩
  calc
    l2 = _ := lm1.symm
    _ = r := lm3

theorem right_unique_at (es: EquivStruct αl αr) (l: αl) (r1 r2: αr) (h1: es.AreCongruence l r1) (h2: es.AreCongruence l r2) : r1 = r2 := right_unique h1 h2

protected theorem symm {es: EquivStruct αl αr} {l: αl} {r: αr} (h: es.AreCongruence l r) : es.symm.AreCongruence r l := by
  refine .mk ?_ ?_ <;> dsimp [EquivStruct.symm]
  · exact h.eq_left
  · exact h.eq_right

theorem symm_iff {es: EquivStruct αl αr} {l: αl} {r: αr} : es.symm.AreCongruence r l ↔ es.AreCongruence l r := by
  constructor
  · intro lm1
    replace lm1 := lm1.symm
    dsimp [EquivStruct.symm_symm] at lm1
    exact lm1
  · intro lm1
    exact lm1.symm

protected theorem trans {es1: EquivStruct αl αr} {es2: EquivStruct αr αr2} {l: αl} {r: αr} {r2: αr2}
  (h1: es1.AreCongruence l r) (h2: es2.AreCongruence r r2) : (es1.trans es2).AreCongruence l r2 := by
  refine .mk ?_ ?_ <;> dsimp [EquivStruct.trans]
  · rw [h1.eq_right]
    exact h2.eq_right
  · rw [h2.eq_left]
    exact h1.eq_left

end AreCongruence


def HasLeftCongruence (es: EquivStruct αl αr) (r: αr) : Prop := ∃(l: αl), es.AreCongruence l r

theorem hasLeftCongruence_iff_eq {es: EquivStruct αl αr} {r: αr} : es.HasLeftCongruence r ↔ (es.toFun (es.invFun r) = r) := by
  constructor
  · rintro ⟨l, lm1, lm2⟩
    rw [lm2]
    exact lm1
  · intro lm1
    dsimp [HasLeftCongruence]
    exists (es.invFun r)
    exact .mk lm1 rfl

theorem hasLeftCongruence_iff_areCongruence {es: EquivStruct αl αr} {r: αr} : es.HasLeftCongruence r ↔ es.AreCongruence (es.invFun r) r := by
  dsimp [HasLeftCongruence]
  constructor
  · rintro ⟨l, lm1⟩
    have lm2 := lm1.eq_left.symm
    subst lm2
    exact lm1
  · intro lm1
    exists (es.invFun r)


def HasRightCongruence (es: EquivStruct αl αr) (l: αl) : Prop := ∃(r: αr), es.AreCongruence l r

theorem hasRightCongruence_iff_eq {es: EquivStruct αl αr} {l: αl} : es.HasRightCongruence l ↔ (es.invFun (es.toFun l) = l) := by
  constructor
  · rintro ⟨r, lm1, lm2⟩
    rw [lm1]
    exact lm2
  · intro lm1
    dsimp [HasRightCongruence]
    exists (es.toFun l)
    exact .mk rfl lm1

theorem hasRightCongruence_iff_areCongruence {es: EquivStruct αl αr} {l: αl} : es.HasRightCongruence l ↔ es.AreCongruence l (es.toFun l) := by
  dsimp [HasRightCongruence]
  constructor
  · rintro ⟨r, lm1⟩
    have lm2 := lm1.eq_right.symm
    subst lm2
    exact lm1
  · intro lm1
    exists (es.toFun l)

namespace HasLeftCongruence

variable {es: EquivStruct αl αr} {r1 r2: αr}

theorem invFun_eq_iff_eq (h1: es.HasLeftCongruence r1) (h2: es.HasLeftCongruence r2) : (es.invFun r1 = es.invFun r2) ↔ r1 = r2 := by
  constructor
  · intro lm1
    replace lm1 := congrArg es.toFun lm1
    rewrite [hasLeftCongruence_iff_eq] at h1 h2
    rewrite [h1, h2] at lm1
    exact lm1
  · intro lm1
    subst lm1
    rfl

end HasLeftCongruence


namespace HasRightCongruence

variable {es: EquivStruct αl αr} {l1 l2: αl}

theorem toFun_eq_iff_eq (h1: es.HasRightCongruence l1) (h2: es.HasRightCongruence l2) : (es.toFun l1 = es.toFun l2) ↔ l1 = l2 := by
  constructor
  · intro lm1
    replace lm1 := congrArg es.invFun lm1
    rewrite [hasRightCongruence_iff_eq] at h1 h2
    rewrite [h1, h2] at lm1
    exact lm1
  · intro lm1
    subst lm1
    rfl

end HasRightCongruence


namespace AreCongruence

variable {es: EquivStruct αl αr} {l: αl} {r: αr}

theorem hasLeftCongruence (h: es.AreCongruence l r) : es.HasLeftCongruence r := Exists.intro _ h

theorem hasRightCongruence (h: es.AreCongruence l r) : es.HasRightCongruence l := Exists.intro _ h

end AreCongruence


inductive AreCongruenceSum (es: EquivStruct αl αr) : (αl ⊕' αr) → (αl ⊕' αr) → Prop where
  | left_left (l: αl) : AreCongruenceSum es (.inl l) (.inl l)
  | right_right (r: αr) : AreCongruenceSum es (.inr r) (.inr r)
  | left_right (l: αl) (r: αr) (req: es.AreCongruence l r) : AreCongruenceSum es (.inl l) (.inr r)
  | right_left (l: αl) (r: αr) (req: es.AreCongruence l r) : AreCongruenceSum es (.inr r) (.inl l)


namespace AreCongruenceSum

@[refl]
protected theorem refl {es: EquivStruct αl αr} (x: (αl ⊕' αr)) : es.AreCongruenceSum x x := by
  rcases x with ⟨l⟩ | ⟨r⟩
  · exact .left_left l
  · exact .right_right r

theorem of_eq {x1 x2: (αl ⊕' αr)} (req: x1 = x2) {es: EquivStruct αl αr} : es.AreCongruenceSum x1 x2 := by
  subst req
  exact AreCongruenceSum.refl _

protected def symm {es: EquivStruct αl αr} (x1 x2: (αl ⊕' αr)) (req: es.AreCongruenceSum x1 x2) : es.AreCongruenceSum x2 x1 := by
  rcases x1 with ⟨l1⟩ | ⟨r1⟩
  <;> rcases x2 with ⟨l2⟩ | ⟨r2⟩
  · cases req
    exact AreCongruenceSum.refl _
  · cases req
    refine .right_left _ _ ?_
    assumption
  · cases req
    refine .left_right _ _ ?_
    assumption
  · cases req
    exact AreCongruenceSum.refl _


theorem equivalence (es: EquivStruct αl αr) : Equivalence (es.AreCongruenceSum) where
  refl := AreCongruenceSum.refl
  symm := AreCongruenceSum.symm _ _
  trans := by
    intro x1 x2 x3 lm1 lm2
    rcases x1 with ⟨l1⟩ | ⟨r1⟩
    <;> rcases x2 with ⟨l2⟩ | ⟨r2⟩
    <;> rcases x3 with ⟨l3⟩ | ⟨r3⟩
    · cases lm1
      cases lm2
      exact AreCongruenceSum.refl _
    · cases lm1
      exact lm2
    · cases lm1
      cases lm2
      refine of_eq ?_
      congr
      refine AreCongruence.left_unique_at es l1 l3 r2 ?_ ?_ <;> assumption
    · cases lm2
      exact lm1
    · cases lm2
      exact lm1
    · cases lm1
      cases lm2
      refine of_eq ?_
      congr
      refine AreCongruence.right_unique_at es l2 r1 r3 ?_ ?_ <;> assumption
    · cases lm1
      exact lm2
    · cases lm1
      cases lm2
      exact AreCongruenceSum.refl _

@[reducible]
def setoidOf (es: EquivStruct αl αr) : Setoid (αl ⊕' αr) := ⟨es.AreCongruenceSum, equivalence es⟩

end AreCongruenceSum

theorem areCongruenceSum_iff {es: EquivStruct αl αr} {x1 x2: (αl ⊕' αr)}
  : es.AreCongruenceSum x1 x2 ↔ (x1 = x2 ∨ ∃(l: αl) (r: αr), (es.AreCongruence l r) ∧ ((x1 = .inl l ∧ x2 = .inr r) ∨ (x1 = .inr r ∧ x2 = .inl l))) := by
  constructor
  · rintro lm1
    rcases lm1 with ⟨l⟩ | ⟨r⟩ | ⟨l, r, lm1⟩ | ⟨l, r, lm1⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · simp [lm1]
    · simp
      exists l
      exists r
  · rintro lm1
    rcases lm1 with lm1 | lm1
    · subst lm1
      exact AreCongruenceSum.refl _
    · rcases lm1 with ⟨l, r, lm1, lm2⟩
      rcases lm2 with ⟨lm2, lm3⟩ | ⟨lm2, lm3⟩
      · subst lm2 lm3
        exact .left_right _ _ lm1
      · subst lm2 lm3
        exact .right_left _ _ lm1


def psumToLeft (es: EquivStruct αl αr) : (αl ⊕' αr) → αl
  | .inl l => l
  | .inr r => es.invFun r

def psumToRight (es: EquivStruct αl αr) : (αl ⊕' αr) → αr
  | .inl l => es.toFun l
  | .inr r => r

def psumToPProd (es: EquivStruct αl αr) (x: (αl ⊕' αr)) : αl ×' αr := ⟨es.psumToLeft x, es.psumToRight x⟩


theorem psumToLeft_left_eq_left_iff_eq {es: EquivStruct αl αr} {l1 l2: αl} : es.psumToLeft (.inl l1) = es.psumToLeft (.inl l2) ↔ l1 = l2 := by
  dsimp [psumToLeft]
  rfl

theorem psumToLeft_left_eq_right_iff_areCongruence {es: EquivStruct αl αr} {l: αl} {r: αr} (req: es.HasLeftCongruence r)
  : (es.psumToLeft (.inl l) = es.psumToLeft (.inr r)) ↔ (es.AreCongruence l r) := by
  dsimp [psumToLeft]
  constructor
  · intro lm1
    subst lm1
    rw [hasLeftCongruence_iff_areCongruence] at req
    exact req
  · intro lm1
    exact lm1.eq_left.symm

theorem psumToLeft_right_eq_right_iff_eq {es: EquivStruct αl αr} {r1 r2: αr} (req1: es.HasLeftCongruence r1) (req2: es.HasLeftCongruence r2)
  : es.psumToLeft (.inr r1) = es.psumToLeft (.inr r2) ↔ r1 = r2 := by
  dsimp [psumToLeft]
  exact req1.invFun_eq_iff_eq req2


theorem psumToRight_left_eq_left_iff_eq {es: EquivStruct αl αr} {l1 l2: αl} (req1: es.HasRightCongruence l1) (req2: es.HasRightCongruence l2)
  : es.psumToRight (.inl l1) = es.psumToRight (.inl l2) ↔ l1 = l2 := by
  dsimp [psumToRight]
  exact req1.toFun_eq_iff_eq req2

theorem psumToRight_left_eq_right_iff_areCongruence {es: EquivStruct αl αr} {l: αl} {r: αr} (req: es.HasRightCongruence l)
  : es.psumToRight (.inl l) = es.psumToRight (.inr r) ↔ (es.AreCongruence l r) := by
  dsimp [psumToRight]
  constructor
  · intro lm1
    rw [← lm1]
    rw [hasRightCongruence_iff_areCongruence] at req
    exact req
  · intro lm1
    exact lm1.eq_right

theorem psumToRight_right_eq_right_iff_eq {es: EquivStruct αl αr} {r1 r2: αr} : (es.psumToRight (.inr r1) = es.psumToRight (.inr r2)) ↔ r1 = r2 := by
  dsimp [psumToRight]
  rfl


theorem psumToPProd_eq_iff_eq_eq {es: EquivStruct αl αr} {ps1 ps2: (αl ⊕' αr)}
  : (es.psumToPProd ps1 = es.psumToPProd ps2) ↔ ((es.psumToLeft ps1 = es.psumToLeft ps2) ∧ (es.psumToRight ps1 = es.psumToRight ps2)) := by
  conv =>
    lhs
    dsimp [psumToPProd]
    rw [PProd.ext_iff]


namespace AreCongruenceSum

variable {es: EquivStruct αl αr} {ps1 ps2: (αl ⊕' αr)}

theorem psumToLeft_eq (h: es.AreCongruenceSum ps1 ps2) : es.psumToLeft ps1 = es.psumToLeft ps2 := by
  rcases h with ⟨l⟩ | ⟨r⟩ | ⟨l, r, lm1⟩ | ⟨l, r, lm1⟩
  · rfl
  · rfl
  · dsimp [psumToLeft]
    exact lm1.eq_left.symm
  · dsimp [psumToLeft]
    exact lm1.eq_left

theorem psumToRight_eq (h: es.AreCongruenceSum ps1 ps2) : es.psumToRight ps1 = es.psumToRight ps2 := by
  rcases h with ⟨l⟩ | ⟨r⟩ | ⟨l, r, lm1⟩ | ⟨l, r, lm1⟩
  · rfl
  · rfl
  · dsimp [psumToRight]
    exact lm1.eq_right
  · dsimp [psumToRight]
    exact lm1.eq_right.symm

theorem psumToPProd_eq (h: es.AreCongruenceSum ps1 ps2) : es.psumToPProd ps1 = es.psumToPProd ps2 := by
  dsimp [psumToPProd]
  refine PProd.ext ?_ ?_ <;> dsimp
  · exact h.psumToLeft_eq
  · exact h.psumToRight_eq



end AreCongruenceSum


theorem areCongruenceSum_iff_psumToPProd_eq {es: EquivStruct αl αr} {x1 x2: (αl ⊕' αr)}
  : es.AreCongruenceSum x1 x2 ↔ (es.psumToPProd x1 = es.psumToPProd x2) := by
  constructor
  · exact AreCongruenceSum.psumToPProd_eq
  · intro lm1
    rcases psumToPProd_eq_iff_eq_eq.mp lm1 with ⟨lm1, lm2⟩
    rcases x1 with ⟨l1⟩ | ⟨r1⟩
    <;> rcases x2 with ⟨l2⟩ | ⟨r2⟩
    <;> (
      dsimp [psumToLeft] at lm1
      dsimp [psumToRight] at lm2 )
    · subst lm1
      rfl
    · refine .left_right _ _ ?_
      exact .mk lm2 lm1.symm
    · refine .right_left _ _ ?_
      exact .mk lm2.symm lm1
    · subst lm2
      rfl

/-
inductive AreCongruenceProd (es: EquivStruct αl αr) (x: αl ×' αr) : Prop where
  | eq_left (req: es.invFun x.snd = x.fst)
  | eq_right (req: es.toFun x.fst = x.snd)
-/

inductive HasSumCongruence (es: EquivStruct αl αr) : (αl ⊕' αr) → Prop where
  | has_left (r: αr) (req: es.HasLeftCongruence r) : HasSumCongruence es (.inr r)
  | has_right (l: αl) (req: es.HasRightCongruence l) : HasSumCongruence es (.inl l)

namespace HasSumCongruence

variable {es: EquivStruct αl αr} {ps: (αl ⊕' αr)}

theorem areCongruence (h: es.HasSumCongruence ps) : es.AreCongruence (es.psumToLeft ps) (es.psumToRight ps) := by
  rcases h with ⟨r, lm1⟩ | ⟨l, lm1⟩
  <;> dsimp [psumToLeft, psumToRight]
  · exact hasLeftCongruence_iff_areCongruence.mp lm1
  · exact hasRightCongruence_iff_areCongruence.mp lm1

theorem hasLeftCongruence {r: αr} (h: es.HasSumCongruence (.inr r)) : es.HasLeftCongruence r := by cases h; assumption

theorem hasRightCongruence {l: αl} (h: es.HasSumCongruence (.inl l)) : es.HasRightCongruence l := by cases h; assumption

end HasSumCongruence

theorem hasSumCongruence_iff_areCongruence {es: EquivStruct αl αr} {ps: (αl ⊕' αr)}
  : es.HasSumCongruence ps ↔ es.AreCongruence (es.psumToLeft ps) (es.psumToRight ps) := by
  constructor
  · exact HasSumCongruence.areCongruence
  · intro lm1
    rcases ps with ⟨l⟩ | ⟨r⟩ <;> dsimp [psumToLeft, psumToRight] at lm1
    · refine .has_right _ ?_
      exact hasRightCongruence_iff_areCongruence.mpr lm1
    · refine .has_left _ ?_
      exact hasLeftCongruence_iff_areCongruence.mpr lm1

theorem hasSumCongruence_iff_hasLeftCongruence {es: EquivStruct αl αr} {r: αr} : es.HasSumCongruence (.inr r) ↔ es.HasLeftCongruence r := by
  constructor
  · exact HasSumCongruence.hasLeftCongruence
  · intro lm1
    exact .has_left _ lm1

theorem hasSumCongruence_iff_hasRightCongruence {es: EquivStruct αl αr} {l: αl} : es.HasSumCongruence (.inl l) ↔ es.HasRightCongruence l := by
  constructor
  · exact HasSumCongruence.hasRightCongruence
  · intro lm1
    exact .has_right _ lm1


def decideHasSumCongruence (es: EquivStruct αl αr) [DecidableEq αl] [DecidableEq αr] : (αl ⊕' αr) → Bool
  | .inl l => decide (es.invFun (es.toFun l) = l)
  | .inr r => decide (es.toFun (es.invFun r) = r)


theorem deciceHasSumCongruence_eq_true_iff_hasSumCongruence {es: EquivStruct αl αr} [DecidableEq αl] [DecidableEq αr] {ps: (αl ⊕' αr)}
  : (es.decideHasSumCongruence ps = .true) ↔ es.HasSumCongruence ps := by
  rcases ps with ⟨l⟩ | ⟨r⟩
  · simp [decideHasSumCongruence]
    rw [hasSumCongruence_iff_hasRightCongruence, hasRightCongruence_iff_eq]
  · simp [decideHasSumCongruence]
    rw [hasSumCongruence_iff_hasLeftCongruence, hasLeftCongruence_iff_eq]


namespace HasSumCongruence

instance decidableHasSumCongruence {es: EquivStruct αl αr} [DecidableEq αl] [DecidableEq αr] {ps: (αl ⊕' αr)} : Decidable (es.HasSumCongruence ps) :=
  decidable_of_iff (es.decideHasSumCongruence ps = .true) deciceHasSumCongruence_eq_true_iff_hasSumCongruence

end HasSumCongruence


end EquivStruct


def ConcreteUnion {αl αr: Sort*} (es: EquivStruct αl αr) : Sort _ := Quotient (EquivStruct.AreCongruenceSum.setoidOf es)

@[defeq]
theorem concreteUnion_def {αl αr: Sort*} {es: EquivStruct αl αr} : ConcreteUnion es = Quotient (EquivStruct.AreCongruenceSum.setoidOf es) := rfl

namespace ConcreteUnion

open EquivStruct

variable {αl αr: Sort*}

def ofPSum (es: EquivStruct αl αr) (x: (αl ⊕' αr)) : ConcreteUnion es := Quotient.mk (AreCongruenceSum.setoidOf es) x

def ofLeft (es: EquivStruct αl αr) (l: αl) : ConcreteUnion es := ofPSum es (.inl l)

def ofRight (es: EquivStruct αl αr) (r: αr) : ConcreteUnion es := ofPSum es (.inr r)

variable {es: EquivStruct αl αr}

@[defeq]
theorem ofLeft_def {l: αl} : ofLeft es l = ofPSum es (.inl l) := rfl

@[defeq]
theorem ofRight_def {r: αr} : ofRight es r = ofPSum es (.inr r) := rfl

theorem ofPSum_eq_iff_areCongruenceSum {x1 x2: (αl ⊕' αr)} : (ofPSum es x1 = ofPSum es x2) ↔ AreCongruenceSum es x1 x2 := by
  dsimp [ofPSum]
  constructor
  · intro lm1
    exact Quotient.exact lm1
  · intro lm1
    exact Quotient.sound lm1


def liftPSum {β: Sort*} (f: (αl ⊕' αr) → β) (req: ∀(x1 x2: (αl ⊕' αr)), es.AreCongruenceSum x1 x2 → f x1 = f x2) (cu: ConcreteUnion es) : β :=
  Quotient.lift f req cu

def toLeft (cu: ConcreteUnion es) : αl := cu.liftPSum (es.psumToLeft) (fun _ _ lm1 => lm1.psumToLeft_eq)

def toRight (cu: ConcreteUnion es) : αr := cu.liftPSum (es.psumToRight) (fun _ _ lm1 => lm1.psumToRight_eq)

def toPProd (cu: ConcreteUnion es) : αl ×' αr := cu.liftPSum es.psumToPProd (fun _ _ lm1 => lm1.psumToPProd_eq)

@[elab_as_elim]
theorem indOfPSum
  {motive: ConcreteUnion es → Prop}
  (ofPSum: (ps: (αl ⊕' αr)) → motive (.ofPSum es ps))
  (t: ConcreteUnion es)
  : motive t := by
  cases t using Quotient.ind
  rename_i ps
  exact ofPSum ps


@[defeq]
theorem liftPSum_ofPSum (es: EquivStruct αl αr) {β: Sort*} (f: (αl ⊕' αr) → β) (req: ∀(x1 x2: (αl ⊕' αr)), es.AreCongruenceSum x1 x2 → f x1 = f x2) (x: (αl ⊕' αr))
  : liftPSum f req (ofPSum es x) = f x := by
  rfl

@[ext]
protected theorem ext {cu1 cu2: ConcreteUnion es} (req1: cu1.toLeft = cu2.toLeft) (req2: cu1.toRight = cu2.toRight) : cu1 = cu2 := by
  cases cu1 using indOfPSum
  cases cu2 using indOfPSum
  rename_i ps1 ps2
  rw [ofPSum_eq_iff_areCongruenceSum, areCongruenceSum_iff_psumToPProd_eq, psumToPProd_eq_iff_eq_eq]
  dsimp [toLeft, liftPSum_ofPSum] at req1
  dsimp [toRight, liftPSum_ofPSum] at req2
  exact ⟨req1, req2⟩

@[defeq]
theorem ofLeft_toLeft_eq_self {l: αl} : (ofLeft es l).toLeft = l := by
  dsimp [ofLeft_def, toLeft, liftPSum_ofPSum, psumToLeft]

@[defeq]
theorem ofRight_toRight_eq_self {r: αr} : (ofRight es r).toRight = r := by
  dsimp [ofRight_def, toRight, liftPSum_ofPSum, psumToRight]

theorem toPProd_eq_toLeft_toRight {cu: ConcreteUnion es} : cu.toPProd = ⟨cu.toLeft, cu.toRight⟩ := by
  cases cu using indOfPSum
  rename_i ps
  dsimp [toLeft, toRight, toPProd, liftPSum_ofPSum, psumToPProd]


theorem toPProd_injective : Function.Injective (toPProd: ConcreteUnion es → αl ×' αr) := by
  intro cu1 cu2 lm1
  simp [toPProd_eq_toLeft_toRight] at lm1
  exact ConcreteUnion.ext lm1.left lm1.right

def isIntersection (cu: ConcreteUnion es) [DecidableEq αl] [DecidableEq αr] : Bool :=
  cu.liftPSum (es.decideHasSumCongruence) (by
    intro ps1 ps2 lm1
    refine Bool.eq_iff_iff.mpr ?_
    simp [deciceHasSumCongruence_eq_true_iff_hasSumCongruence]
    rcases lm1 with ⟨l⟩ | ⟨r⟩ | ⟨l, r, lm1⟩ | ⟨l, r, lm1⟩
    · rfl
    · rfl
    · simp [hasSumCongruence_iff_hasLeftCongruence, hasSumCongruence_iff_hasRightCongruence, lm1.hasLeftCongruence, lm1.hasRightCongruence]
    · simp [hasSumCongruence_iff_hasLeftCongruence, hasSumCongruence_iff_hasRightCongruence, lm1.hasLeftCongruence, lm1.hasRightCongruence] )


theorem isIntersection_eq_true_iff_areCongruence {cu: ConcreteUnion es} [DecidableEq αl] [DecidableEq αr]
  : (cu.isIntersection = .true) ↔ (es.AreCongruence cu.toLeft cu.toRight) := by
  cases cu using indOfPSum
  rename_i ps
  dsimp [toLeft, toRight, isIntersection, liftPSum_ofPSum]
  rw [deciceHasSumCongruence_eq_true_iff_hasSumCongruence]
  exact hasSumCongruence_iff_areCongruence


instance decidableAreCongruence {cu: ConcreteUnion es} [DecidableEq αl] [DecidableEq αr] : Decidable (es.AreCongruence cu.toLeft cu.toRight) := decidable_of_decidable_of_iff isIntersection_eq_true_iff_areCongruence




/-
theorem toLeft_injective : Function.Injective (toLeft: ConcreteUnion es → αl) := by
  intro cu1 cu2 lm1
  cases cu1 using indOfPSum
  cases cu2 using indOfPSum
  rename_i ps1 ps2
  dsimp [toLeft, liftPSum_ofPSum] at lm1
  rw [ofPSum_eq_iff_areCongruenceSum]
  rcases ps1 with ⟨l1⟩ | ⟨r1⟩
  <;> rcases ps2 with ⟨l2⟩ | ⟨r2⟩
  <;> (dsimp [psumToLeft] at lm1)
  · subst lm1; rfl
  · refine .left_right _ _ ?_
-/
/-
theorem toLeft_eq_iff_toRight_eq {cu1 cu2: ConcreteUnion es} : (cu1.toLeft = cu2.toLeft) ↔ (cu1.toRight = cu2.toRight) := by
  cases cu1 using indOfPSum
  cases cu2 using indOfPSum
  rename_i ps1 ps2
-/
/-
theorem ofLeft_eq_ofLeft_iff_eq {l1 l2: αl} : (ofLeft es l1 = ofLeft es l2) ↔ l1 = l2 := by
  dsimp [ofLeft_def]
  rw [ofPSum_eq_iff_areCongruenceSum]
  constructor
  · intro lm1
    cases lm1
    rfl
  · intro lm1
    subst lm1
    rfl
-/


end ConcreteUnion


end Nemonuri.Relations.Heterogeneous

end
