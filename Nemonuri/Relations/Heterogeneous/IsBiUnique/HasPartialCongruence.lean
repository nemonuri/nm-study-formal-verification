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

theorem leftOfRel?_eq_some_iff_rel {rel: αl → αr → Prop} [HasPartialCongruence rel] {l: αl} {r: αr}
  : (HasPartialCongruence.leftOfRel? rel r = .some l) ↔ rel l r := by
  have lm1 := isPartialCongruence_of_rel rel
  dsimp [leftOfRel?, PartialCongruence.ofRel]
  exact lm1.left?_eq_some_iff_rel _ _


def rightOfRel (rel: αl → αr → Prop) [HasPartialCongruence rel] (l: αl) (req: ∃r, rel l r) : αr := (isPartialCongruence_of_rel rel).right l req

def leftOfRel (rel: αl → αr → Prop) [HasPartialCongruence rel] (r: αr) (req: ∃l, rel l r) : αl := (isPartialCongruence_of_rel rel).left r req

end HasPartialCongruence


end Nemonuri.Relations.Heterogeneous

end
