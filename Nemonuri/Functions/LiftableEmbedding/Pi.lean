module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

variable {L R: Sort*}

def comapPi (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) (pir: (rv: R) → mr rv) (lv: L) : mr (lem lv) := pir (lem lv)

@[defeq]
theorem comapPi_eq {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} {pir: (rv: R) → mr rv} {lv: L}
  : lem.comapPi mr pir lv = pir (lem lv) := by
  dsimp [comapPi]

noncomputable def embedPiOfNonempty (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) (compl: ∀(rv: R), (¬lem.IsLiftable rv) → Nonempty (mr rv)) (pi: (lv: L) → (mr (lem lv))) (rv: R) : mr rv :=
  if lm1: lem.IsLiftable rv then
    have lm2: lem lm1.lift = rv := lm1.lift_apply_eq_self
    lm2.ndrec (pi lm1.lift)
  else
    Classical.choice (compl rv lm1)

theorem comapPi_embedPiOfNonempty_leftInverse {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} (compl: ∀(rv: R), (¬lem.IsLiftable rv) → Nonempty (mr rv))
  : Function.LeftInverse (lem.comapPi mr) (lem.embedPiOfNonempty mr compl) := by
  intro pil
  simp only [funext_iff]
  intro lv
  dsimp [comapPi_eq, embedPiOfNonempty]
  simp [IsLiftable.of_apply]
  exact IsLiftable.pi_lift_eq_self

theorem comapPi_surjective {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} (req: ∀(rv: R), (¬lem.IsLiftable rv) → Nonempty (mr rv)) : Function.Surjective (lem.comapPi mr) :=
  (lem.comapPi_embedPiOfNonempty_leftInverse req).surjective


structure Complement (lem: LiftableEmbedding L R) (mr: (rv: R) → Sort*) where
  ofFun :: toFun (pil: (lv: L) → mr (lem lv)) (rv: R) (req: ¬lem.IsLiftable rv) : mr rv

namespace Complement

variable {lem: LiftableEmbedding L R} {mr: (rv: R) → Sort*} [DecidablePred (lem.IsLiftable ·)]

def embedPi (co: lem.Complement mr) (pi: (lv: L) → mr (lem lv)) (rv: R) : mr rv :=
  if lm1: lem.IsLiftable rv then
    have lm2: lem lm1.lift = rv := lm1.lift_apply_eq_self
    lm2.ndrec (pi lm1.lift)
  else
    co.toFun pi rv lm1

theorem embedPi_eq {co: lem.Complement mr} {pi: (lv: L) → mr (lem lv)} {lv: L} : co.embedPi pi (lem lv) = pi lv := by
  simp [embedPi, IsLiftable.of_apply]
  exact IsLiftable.pi_lift_eq_self


theorem comapPi_embedPi_leftInverse {co: lem.Complement mr} : Function.LeftInverse (lem.comapPi mr) (co.embedPi) := by
  intro pil
  simp only [funext_iff]
  intro lv
  dsimp [comapPi_eq]
  exact co.embedPi_eq


theorem embedPi_injective {co: lem.Complement mr} : Function.Injective co.embedPi := co.comapPi_embedPi_leftInverse.injective

--theorem toFun_apply_eq_of_isLiftable {co: lem.Complement mr} {pir: (rv: R) → mr rv} (req1: lem.IsLiftable pir) (rv: R) (req2: ¬lem.)

end Complement


def ofPi (lem: LiftableEmbedding L R) [DecidablePred (lem.IsLiftable ·)] (mr: (rv: R) → Sort*) (co: lem.Complement mr) : LiftableEmbedding ((lv: L) → mr (lem lv)) ((rv: R) → mr rv) where
  embed := co.embedPi
  lift pir _ := lem.comapPi mr pir
  valid := by
    refine .mk ?_
    dsimp [RestrictedLeftInverse]
    exact co.comapPi_embedPi_leftInverse


theorem ofPi_isLiftable_iff {lem: LiftableEmbedding L R} [DecidablePred (lem.IsLiftable ·)] {mr: (rv: R) → Sort*} {co: lem.Complement mr} {pir: (rv: R) → mr rv}
  : (lem.ofPi mr co).IsLiftable pir ↔ (∀(rv: R), (req: ¬lem.IsLiftable rv) → pir rv = co.toFun (lem.comapPi mr pir) rv req) := by
  constructor
  · intro lm1 rv lm2
    cases lm1 using IsLiftable.induction
    rename_i pil lm1
    subst lm1
    dsimp [coe_def, ofPi]
    rw [co.comapPi_embedPi_leftInverse.eq pil]
    simp [Complement.embedPi, lm2]
  · intro lm1
    simp [isLiftable_iff_left_exists]
    exists (lem.comapPi mr pir)
    dsimp [coe_def, ofPi]
    simp only [funext_iff]
    intro rv
    specialize lm1 rv
    by_cases lm2: lem.IsLiftable rv
    · cases lm2 using IsLiftable.induction
      rename_i lv lm2
      subst lm2
      rw [co.embedPi_eq, lem.comapPi_eq]
    · specialize lm1 lm2
      refine Eq.trans lm1 ?_
      simp [Complement.embedPi, lm2]



end Nemonuri.Functions.LiftableEmbedding

end
