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

end HasPartialCongruence


end Nemonuri.Relations.Heterogeneous

end
