module

public import Nemonuri.Relations.Heterogeneous.IsBiUnique.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

class HasPartialCongruence {αl αr: Type*} (rel: αl → αr → Prop) where
  partialCongruence: PartialCongruence rel

namespace PartialCongruence

variable {αl αr: Type*}

def ofRel (rel: αl → αr → Prop) [i: HasPartialCongruence rel] : PartialCongruence rel := i.partialCongruence

open Classical in
noncomputable def ofClassical (rel: αl → αr → Prop) [IsBiUnique rel] : PartialCongruence rel where
  right? l := if lm1: ∃(r: αr), rel l r then .some lm1.choose else .none
  left? r := if lm1: ∃(l: αl), rel l r then .some lm1.choose else .none
  valid := by
    refine .mk ?_ ?_ <;> (dsimp; intro l r; simp)
    · constructor
      · rintro ⟨lm1, lm2⟩
        rw [← lm2]
        exact lm1.choose_spec
      · intro lm1
        have lm2 : Exists (rel l) := Exists.intro r lm1
        exists lm2
        have lm3 := lm2.choose_spec
        have lm4 := IsBiUnique.rightUnique lm1 lm3
        exact lm4.symm
    · constructor
      · rintro ⟨lm1, lm2⟩
        rw [← lm2]
        exact lm1.choose_spec
      · intro lm1
        have lm2 : Exists (rel · r) := Exists.intro l lm1
        exists lm2
        have lm3 := lm2.choose_spec
        have lm4 := IsBiUnique.leftUnique lm1 lm3
        exact lm4.symm

end PartialCongruence


namespace HasPartialCongruence

variable {αl αr: Type*}

@[reducible]
noncomputable def ofClassical (rel: αl → αr → Prop) [IsBiUnique rel] : HasPartialCongruence rel := ⟨PartialCongruence.ofClassical rel⟩

def rightOfRel? (rel: αl → αr → Prop) [HasPartialCongruence rel] (l: αl) : Option αr := (PartialCongruence.ofRel rel).right? l

def leftOfRel? (rel: αl → αr → Prop) [HasPartialCongruence rel] (r: αr) : Option αl := (PartialCongruence.ofRel rel).left? r

theorem isPartialCongruence_of_rel (rel: αl → αr → Prop) [i: HasPartialCongruence rel] : IsPartialCongruence (i.partialCongruence.toStruct) rel := i.partialCongruence.valid


theorem rightOfRel?_eq_some_iff_rel {rel: αl → αr → Prop} [HasPartialCongruence rel] {l: αl} {r: αr}
  : (HasPartialCongruence.rightOfRel? rel l = .some r) ↔ rel l r := by
  have lm1 := isPartialCongruence_of_rel rel
  dsimp [rightOfRel?, PartialCongruence.ofRel]
  exact lm1.right?_eq_some_iff_rel _ _

theorem rightOfRel?_eq_none_iff_not_rel {rel: αl → αr → Prop} [HasPartialCongruence rel] {l: αl}
  : (HasPartialCongruence.rightOfRel? rel l = .none) ↔ (∀r, ¬rel l r) := by
  have lm1 := isPartialCongruence_of_rel rel
  dsimp [rightOfRel?, PartialCongruence.ofRel]
  exact lm1.right?_eq_none_iff_forall_not_rel

theorem leftOfRel?_eq_some_iff_rel {rel: αl → αr → Prop} [HasPartialCongruence rel] {l: αl} {r: αr}
  : (HasPartialCongruence.leftOfRel? rel r = .some l) ↔ rel l r := by
  have lm1 := isPartialCongruence_of_rel rel
  dsimp [leftOfRel?, PartialCongruence.ofRel]
  exact lm1.left?_eq_some_iff_rel _ _

theorem leftOfRel?_eq_none_iff_not_rel {rel: αl → αr → Prop} [HasPartialCongruence rel] {r: αr}
  : (HasPartialCongruence.leftOfRel? rel r = .none) ↔ (∀l, ¬rel l r) := by
  have lm1 := isPartialCongruence_of_rel rel
  dsimp [leftOfRel?, PartialCongruence.ofRel]
  exact lm1.left?_eq_none_iff_forall_not_rel


def rightOfRel (rel: αl → αr → Prop) [HasPartialCongruence rel] (l: αl) (req: ∃r, rel l r) : αr := (isPartialCongruence_of_rel rel).right l req

def leftOfRel (rel: αl → αr → Prop) [HasPartialCongruence rel] (r: αr) (req: ∃l, rel l r) : αl := (isPartialCongruence_of_rel rel).left r req

section HEqSection

variable {rel: αl → αr → Prop} [HasPartialCongruence rel]


variable (rel) in
def areHEqOnLeft [DecidableEq αl] (l: αl) (r: αr) : Bool :=
  match HasPartialCongruence.leftOfRel? rel r with
  | .some v => decide (l = v)
  | .none => .false


variable (rel) in
def areHEqOnRight [DecidableEq αr] (l: αl) (r: αr) : Bool :=
  match HasPartialCongruence.rightOfRel? rel l with
  | .some v => decide (r = v)
  | .none => .false


theorem areHEqOnLeft_eq_true_iff [IsBiUnique rel] [DecidableEq αl] {l: αl} {r: αr} : (areHEqOnLeft rel l r = .true) ↔ rel l r := by
  dsimp [areHEqOnLeft]
  split <;> (rename_i lm1; simp)
  · rename_i v
    simp [HasPartialCongruence.leftOfRel?_eq_some_iff_rel] at lm1
    constructor
    · intro lm2
      subst lm2
      exact lm1
    · intro lm2
      exact IsBiUnique.leftUnique lm2 lm1
  · simp [Option.eq_none_iff_forall_ne_some, HasPartialCongruence.leftOfRel?_eq_some_iff_rel] at lm1
    exact lm1 l


theorem areHEqOnRight_eq_true_iff [IsBiUnique rel] [DecidableEq αr] {l: αl} {r: αr} : (areHEqOnRight rel l r = .true) ↔ rel l r := by
  dsimp [areHEqOnRight]
  split <;> (rename_i lm1; simp)
  · rename_i v
    simp [HasPartialCongruence.rightOfRel?_eq_some_iff_rel] at lm1
    constructor
    · intro lm2
      subst lm2
      exact lm1
    · intro lm2
      exact IsBiUnique.rightUnique lm2 lm1
  · simp [Option.eq_none_iff_forall_ne_some, HasPartialCongruence.rightOfRel?_eq_some_iff_rel] at lm1
    exact lm1 r

variable (rel) in
@[reducible]
def decidableRelOnLeft [IsBiUnique rel] [DecidableEq αl] : DecidableRel rel := fun _ _ => decidable_of_decidable_of_iff areHEqOnLeft_eq_true_iff

variable (rel) in
@[reducible]
def decidableRelOnRight [IsBiUnique rel] [DecidableEq αr] : DecidableRel rel := fun _ _ => decidable_of_decidable_of_iff areHEqOnRight_eq_true_iff

end HEqSection


end HasPartialCongruence


end Nemonuri.Relations.Heterogeneous

end
