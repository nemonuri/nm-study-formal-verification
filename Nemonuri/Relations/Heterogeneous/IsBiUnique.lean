module

public import Mathlib.Logic.Relator


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous



class IsBiUnique {αl αr: Sort*} (rel: αl → αr → Prop) : Prop where
  biUnique : Relator.BiUnique rel

namespace IsBiUnique

variable {αl αr: Sort*} {rel: αl → αr → Prop} [IsBiUnique rel]

theorem leftUnique {l1 l2: αl} {r: αr} (req1: rel l1 r) (req2: rel l2 r) : l1 = l2 := IsBiUnique.biUnique.left req1 req2

theorem rightUnique {l: αl} {r1 r2: αr} (req1: rel l r1) (req2: rel l r2) : r1 = r2 := IsBiUnique.biUnique.right req1 req2

theorem left_eq_iff_rel {l: αl} {r: αr} (req: rel l r) (l2: αl) : (l = l2) ↔ rel l2 r := by
  constructor
  · intro lm1; subst lm1; exact req
  · intro lm1
    exact leftUnique req lm1

theorem right_eq_iff_rel {l: αl} {r: αr} (req: rel l r) (r2: αr) : (r = r2) ↔ rel l r2 := by
  constructor
  · intro lm1; subst lm1; exact req
  · intro lm1
    exact rightUnique req lm1

theorem left_eq_iff_right_eq_of_rel₂ {l1 l2: αl} {r1 r2: αr} (req1: rel l1 r1) (req2: rel l2 r2) : (l1 = l2) ↔ (r1 = r2) := by
  constructor
  · intro lm1
    subst lm1
    exact rightUnique req1 req2
  · intro lm1
    subst lm1
    exact leftUnique req1 req2

theorem rel_iff_rel_of_rel₂ {l1 l2: αl} {r1 r2: αr} (req1: rel l1 r1) (req2: rel l2 r2) : rel l1 r2 ↔ rel l2 r1 := by
  have lm1 := left_eq_iff_right_eq_of_rel₂ req1 req2
  constructor
  · intro lm2
    have lm3 := rightUnique req1 lm2
    subst lm3
    exact req2
  · intro lm2
    have lm3 := leftUnique req1 lm2
    subst lm3
    exact req2

end IsBiUnique


structure BiUniqueIndicator (αl αr: Type*) where
  indicate : αl → αr → Bool
  valid: Relator.BiUnique (indicate · · = .true)


namespace BiUniqueIndicator

variable {αl αr: Type*}

def Rel (bui: BiUniqueIndicator αl αr) (l: αl) (r: αr) : Prop := bui.indicate l r = .true

@[defeq]
theorem rel_def {bui: BiUniqueIndicator αl αr} {l: αl} {r: αr} : bui.Rel l r = (bui.indicate l r = .true) := rfl

instance {bui: BiUniqueIndicator αl αr} : DecidableRel (bui.Rel) := fun _ _ => decidable_of_decidable_of_eq rel_def.symm

instance {bui: BiUniqueIndicator αl αr} : IsBiUnique bui.Rel where
  biUnique := bui.valid

end BiUniqueIndicator


end Nemonuri.Relations.Heterogeneous

end
