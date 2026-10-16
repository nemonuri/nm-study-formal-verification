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

structure PartialCongruenceStruct (αl αr: Type*) where
  right?: αl → Option αr
  left?: αr → Option αl

structure IsPartialCongruence {αl αr: Type*} (s: PartialCongruenceStruct αl αr) (rel: αl → αr → Prop) where
  right?_eq_some_iff_rel (l: αl) (r: αr) : (s.right? l = .some r) ↔ (rel l r)
  left?_eq_some_iff_rel (l: αl) (r: αr) : (s.left? r = .some l) ↔ (rel l r)

structure PartialCongruence {αl αr: Type*} (rel: αl → αr → Prop) extends toStruct: PartialCongruenceStruct αl αr where
  valid: IsPartialCongruence toStruct rel


namespace IsPartialCongruence

variable {αl αr: Type*} {rel: αl → αr → Prop} {pcs: PartialCongruenceStruct αl αr}


theorem right?_eq_some_of_rel (h: IsPartialCongruence pcs rel) {l: αl} {r: αr} (req: rel l r) : pcs.right? l = .some r :=
  (h.right?_eq_some_iff_rel _ _).mpr req

theorem left?_eq_some_of_rel (h: IsPartialCongruence pcs rel) {l: αl} {r: αr} (req: rel l r) : pcs.left? r = .some l :=
  (h.left?_eq_some_iff_rel _ _).mpr req

theorem rel_of_right?_eq_some (h: IsPartialCongruence pcs rel) {l: αl} {r: αr} (req: pcs.right? l = .some r) : rel l r :=
  (h.right?_eq_some_iff_rel _ _).mp req

theorem rel_of_left?_eq_some (h: IsPartialCongruence pcs rel) {l: αl} {r: αr} (req: pcs.left? r = .some l) : rel l r :=
  (h.left?_eq_some_iff_rel _ _).mp req

/-
theorem not_rel_of_right?_eq_none (h: IsPartialCongruence pcs rel) {l: αl} (req: pcs.right? l = .none) (r: αr) : ¬rel l r := by
  intro lm1
  have lm2 := h.right?_eq_some_of_rel lm1
  simp [lm2] at req

theorem not_rel_of_left?_eq_none (h: IsPartialCongruence pcs rel) {r: αr} (req: pcs.left? r = .none) (l: αl) : ¬rel l r := by
  intro lm1
  have lm2 := h.left?_eq_some_of_rel lm1
  simp [lm2] at req
-/


theorem right?_eq_some_iff_left?_eq_some (h: IsPartialCongruence pcs rel) {l: αl} {r: αr} : (pcs.right? l = .some r) ↔ (pcs.left? r = .some l) :=
  (h.right?_eq_some_iff_rel l r).trans (h.left?_eq_some_iff_rel l r).symm



theorem right?_eq_none_iff_forall_not_rel (h: IsPartialCongruence pcs rel) {l: αl} : (pcs.right? l = .none) ↔ (∀r, ¬rel l r) := by
  rw [Option.eq_none_iff_forall_ne_some]
  refine forall_congr' ?_
  intro r
  dsimp
  classical
  refine Decidable.not_iff_not.mpr ?_
  exact h.right?_eq_some_iff_rel _ _

theorem left?_eq_none_iff_forall_not_rel (h: IsPartialCongruence pcs rel) {r: αr} : (pcs.left? r = .none) ↔ (∀l, ¬rel l r) := by
  rw [Option.eq_none_iff_forall_ne_some]
  refine forall_congr' ?_
  intro l
  dsimp
  classical
  refine Decidable.not_iff_not.mpr ?_
  exact h.left?_eq_some_iff_rel _ _


theorem right_unique_rel (h: IsPartialCongruence pcs rel) {l: αl} {r1 r2: αr} (req1: rel l r1) (req2: rel l r2) : r1 = r2 := by
  have lm1 := h.right?_eq_some_of_rel req1
  have lm2 := h.right?_eq_some_of_rel req2
  have lm3 := lm1.symm.trans lm2
  simpa using lm3

theorem left_unique_rel (h: IsPartialCongruence pcs rel) {l1 l2: αl} {r: αr} (req1: rel l1 r) (req2: rel l2 r) : l1 = l2 := by
  have lm1 := h.left?_eq_some_of_rel req1
  have lm2 := h.left?_eq_some_of_rel req2
  have lm3 := lm1.symm.trans lm2
  simpa using lm3

theorem biUnique_rel (h: IsPartialCongruence pcs rel) : Relator.BiUnique rel := by
  refine ⟨?_, ?_⟩
  · dsimp [Relator.LeftUnique]
    exact @h.left_unique_rel
  · dsimp [Relator.RightUnique]
    exact @h.right_unique_rel



end IsPartialCongruence


namespace PartialCongruence

variable {αl αr: Type*} {rel: αl → αr → Prop}

instance subsingleton : Subsingleton (PartialCongruence rel) where
  allEq := by
    rintro ⟨⟨r1, l1⟩, lm1_1, lm1_2⟩ ⟨⟨r2, l2⟩, lm2_1, lm2_2⟩
    dsimp at lm1_1 lm1_2 lm2_1 lm2_2
    simp [funext_iff]
    refine ⟨?_, ?_⟩
    · intro l
      specialize lm1_1 l
      specialize lm2_1 l
      rcases lm3: r1 l with _ | ⟨r⟩
      · simp [lm3] at lm1_1
        simp [lm1_1, ← Option.eq_none_iff_forall_ne_some] at lm2_1
        exact lm2_1.symm
      · specialize lm1_1 r
        specialize lm2_1 r
        simp [lm3] at lm1_1
        simp [lm1_1] at lm2_1
        exact lm2_1.symm
    · intro r
      replace lm1_2 l := lm1_2 l r
      replace lm2_2 l := lm2_2 l r
      rcases lm3: l1 r with _ | ⟨l⟩
      · simp [lm3] at lm1_2
        simp [lm1_2, ← Option.eq_none_iff_forall_ne_some] at lm2_2
        exact lm2_2.symm
      · specialize lm1_2 l
        specialize lm2_2 l
        simp [lm3] at lm1_2
        simp [lm1_2] at lm2_2
        exact lm2_2.symm

theorem isBiUnique (pc: PartialCongruence rel) : IsBiUnique rel := ⟨pc.valid.biUnique_rel⟩

end PartialCongruence

class HasPartialCongruence {αl αr: Type*} (rel: αl → αr → Prop) where
  partialCongruence: PartialCongruence rel

namespace PartialCongruence

variable {αl αr: Type*}

def ofRel (rel: αl → αr → Prop) [i: HasPartialCongruence rel] : PartialCongruence rel := i.partialCongruence

end PartialCongruence

end Nemonuri.Relations.Heterogeneous

end
