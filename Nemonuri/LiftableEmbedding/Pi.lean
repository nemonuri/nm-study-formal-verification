module

public import Nemonuri.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.LiftableEmbedding


variable {L R: Type*}

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


theorem embedPi_injective {l: LiftableEmbedding L R} {m: R → Sort*} : Function.Injective (l.embedPi m) := by
  intro pi1 pi2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  have lm2 := l.liftable_of_apply lv
  specialize lm1 (l lv) lm2
  simp [embedPi_eq] at lm1
  exact lm1


def restrictPi (l: LiftableEmbedding L R) (m: R → Sort*) (pi: (rv: R) → m rv) (rv: R) (_: l.IsLiftable rv) : m rv := pi rv


def liftPi (l: LiftableEmbedding L R) (m: R → Sort*) (pi: (rv: R) → m rv) (lv: L) : m (l lv) := pi (l lv)


  --let pir := l.lift

def liftRestrictedPi (l: LiftableEmbedding L R) (m: R → Sort*) (pi: (rv: R) → (req: l.IsLiftable rv) → m rv) (lv: L) : m (l lv) := pi (l lv) .of_apply


theorem liftRestrictedPi_injective {l: LiftableEmbedding L R} {m: R → Sort*} : Function.Injective (l.liftRestrictedPi m) := by
  intro pir1 pir2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro rv lm2
  cases lm2 using IsLiftable.induction
  rename_i lv lm2
  specialize lm1 lv
  dsimp [liftRestrictedPi] at lm1
  subst lm2
  exact lm1

/- (mr: (rv: R) → (req: ¬l.IsLiftable rv) → Sort u)  -/

def embedMotive.{u} (l: LiftableEmbedding L R) [DecidablePred (l.IsLiftable ·)] (ml: L → Sort u) (rv: R) : Sort u :=
  if lm1: l.IsLiftable rv then ml lm1.lift else PUnit.{u} --mr rv lm1

theorem embedMotive_eq.{u} {l: LiftableEmbedding L R} [DecidablePred (l.IsLiftable ·)] {ml: L → Sort u} {lv: L}
  : l.embedMotive ml (l lv) = ml lv := by
  simp [embedMotive, lift_to_left_norm]

theorem embedMotive_injective {l: LiftableEmbedding L R} [DecidablePred (l.IsLiftable ·)] : Function.Injective (l.embedMotive) := by
  intro lv1 lv2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  specialize lm1 (l lv)
  simpa [embedMotive_eq] using lm1


  --simp only [funext_iff]

  --dsimp [liftPi]


def liftMotive.{u} (l: LiftableEmbedding L R) (mr: R → Sort u) (lv: L) : Sort u := mr (l lv)

theorem liftMotive_embedMotive_leftInverse {l: LiftableEmbedding L R} [DecidablePred (l.IsLiftable ·)] : Function.LeftInverse l.liftMotive l.embedMotive := by
  intro pil
  simp only [funext_iff]
  intro lv
  dsimp [liftMotive]
  exact embedMotive_eq

def ofMotive.{u} (l: LiftableEmbedding L R) [DecidablePred (l.IsLiftable ·)] : LiftableEmbedding (L → Sort u) (R → Sort u) :=
  .ofInjective (L → Sort u) (R → Sort u) (l.embedMotive) l.embedMotive_injective (fun rv => l.liftMotive rv.val)
               (by dsimp; exact l.liftMotive_embedMotive_leftInverse)



def embedPi₂ (l: LiftableEmbedding L R) [DecidablePred (l.IsLiftable ·)] (ml: L → Sort*) (pi: (lv: L) → ml lv) (rv: R) : l.embedMotive ml rv :=
  if lm1: l.IsLiftable rv then
    have lm2_1: ml lm1.lift = l.embedMotive ml rv := by simp [embedMotive, lm1]
    pi lm1.lift |> cast lm2_1
  else
    have lm2_2: PUnit = l.embedMotive ml rv := by simp [embedMotive, lm1]
    PUnit.unit |> cast lm2_2

theorem embedPi₂_heq {l: LiftableEmbedding L R} [DecidablePred (l.IsLiftable ·)] {ml: L → Sort*} (pi: (lv: L) → ml lv) (lv: L)
  : l.embedPi₂ ml pi (l lv) ≍ pi lv := by
  simp [embedPi₂, lift_to_left_norm]
  have lm1 := l.liftable_of_apply lv
  have lm2 := lm1.lift_eq_self
  have lm3 := congrArg ml lm2
  have lm4 := lm2.rec (motive := fun lv0 refl0 => (req4_1: ml lm1.lift = ml lv0) → (cast req4_1 (pi lm1.lift) = pi lv0)) ?h1
  case h1 => simp
  specialize lm4 lm3
  exact heq_of_cast_eq _ lm4

theorem embedPi₂_injective {l: LiftableEmbedding L R} [DecidablePred (l.IsLiftable ·)] {ml: L → Sort*} : Function.Injective (l.embedPi₂ ml) := by
  intro pi1 pi2 lm1
  simp only [funext_iff] at ⊢ lm1
  intro lv
  specialize lm1 (l lv)
  have lm2 := (l.embedPi₂_heq pi1 lv).symm.trans (heq_of_eq lm1)
  replace lm2 := lm2.trans (l.embedPi₂_heq pi2 lv)
  exact eq_of_heq lm2


def liftPi₂ (l: LiftableEmbedding L R) [DecidablePred (l.IsLiftable ·)] (mr: R → Sort*) (pi: (rv: R) → mr rv) (lv: L) : l.liftMotive mr lv := pi (l lv)

theorem liftPi₂_embedPi₂_leftInverse {l: LiftableEmbedding L R} [DecidablePred (l.IsLiftable ·)] {ml: L → Sort*} {pi: (lv: L) → ml lv} {lv: L}
  : l.liftPi₂ (l.embedMotive ml) (l.embedPi₂ ml pi) lv ≍ pi lv := by
  refine heq_of_cast_eq ?_ ?_
  · rw [l.liftMotive_embedMotive_leftInverse ml]
  · dsimp [liftPi₂]
    rw [cast_eq_iff_heq]
    exact embedPi₂_heq _ _



--def embedPi₃.{u} (l: LiftableEmbedding L R) [DecidablePred (l.IsLiftable ·)] (mr: R → Sort u) (pi: (lv: L) → (mr (l lv))) (rv: R) : mr rv :=

/-
theorem liftPi_surjective {l: LiftableEmbedding L R} {m: R → Sort*} : Function.Surjective (l.liftPi m) := by
  intro pil
  let dpred : DecidablePred (l.IsLiftable ·) := fun _ => Classical.propDecidable _
  let pir := l.embedPi₂ (fun lv => m (l lv)) pil
-/


end Nemonuri.LiftableEmbedding

end
