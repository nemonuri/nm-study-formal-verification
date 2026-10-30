module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} {rel: αl → αr → Prop}

namespace SumUnion

theorem projectSetToRightSet_setOfRightSet_subset [IsBiUnique rel] {sus: Set (SumUnion rel)} : setOfRightSet rel (projectSetToRightSet sus) ⊆ sus := by
  dsimp [Set.subset_def]
  intro su lm1
  cases su using indOfSum
  rename_i s
  rcases s with ⟨l⟩ | ⟨r⟩
  · simp [setOfRightSet_mem_inl_iff_mem, projectSetToRightSet_mem_eq_mem] at lm1
    rcases lm1 with ⟨r, lm1, lm2⟩
    replace lm2 := (ofSum_eq_iff_sumEquivGen.mpr ∘ sumEquivGen_inl_inr_iff.mpr) lm2
    rw [lm2]
    exact lm1
  · simp [setOfRightSet_mem_inr_iff_mem, projectSetToRightSet_mem_eq_mem] at lm1
    exact lm1

theorem projectSetToLeftSet_setOfLeftSet_subset [IsBiUnique rel] {sus: Set (SumUnion rel)} : setOfLeftSet rel (projectSetToLeftSet sus) ⊆ sus := by
  dsimp [Set.subset_def]
  intro su lm1
  cases su using indOfSum
  rename_i s
  rcases s with ⟨l⟩ | ⟨r⟩
  · simp [setOfLeftSet_mem_inl_iff_mem, projectSetToLeftSet_mem_eq_mem] at lm1
    exact lm1
  · simp [setOfLeftSet_mem_inr_iff_mem, projectSetToLeftSet_mem_eq_mem] at lm1
    rcases lm1 with ⟨l, lm1, lm2⟩
    replace lm2 := (ofSum_eq_iff_sumEquivGen.mpr ∘ sumEquivGen_inr_inl_iff.mpr) lm2
    rw [lm2]
    exact lm1

def projectSetToIntersection (sus: Set (SumUnion rel)) : Set (SumUnion rel) :=
  (setOfLeftSet rel (projectSetToLeftSet sus)) ∩ (setOfRightSet rel (projectSetToRightSet sus))

theorem projectSetToIntersection_inl_mem_iff [IsBiUnique rel] {l: αl} {sus: Set (SumUnion rel)}
  : (.ofSum (.inl l) ∈ projectSetToIntersection sus) ↔ (.ofSum (.inl l) ∈ sus ∧ ∃ r, .ofSum (.inr r) ∈ sus ∧ rel l r) := by
  simp [projectSetToIntersection, setOfLeftSet_mem_inl_iff_mem, setOfRightSet_mem_inl_iff_mem]
  dsimp [projectSetToLeftSet_mem_eq_mem, projectSetToRightSet_mem_eq_mem]
  rfl

theorem projectSetToIntersection_inr_mem_iff [IsBiUnique rel] {r: αr} {sus: Set (SumUnion rel)}
  : (.ofSum (.inr r) ∈ projectSetToIntersection sus) ↔ (.ofSum (.inr r) ∈ sus ∧ ∃ l, .ofSum (.inl l) ∈ sus ∧ rel l r) := by
  simp [projectSetToIntersection, setOfLeftSet_mem_inr_iff_mem, setOfRightSet_mem_inr_iff_mem]
  dsimp [projectSetToLeftSet_mem_eq_mem, projectSetToRightSet_mem_eq_mem]
  conv => lhs; rw [And.comm]

theorem exists_eq_of_forall_projectSetToIntersection_mem [IsBiUnique rel] {sus: Set (SumUnion rel)} : (∀su ∈ projectSetToIntersection sus, ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r)) := by
  intro su lm1
  cases su using indOfSum
  rename_i s
  rcases s with ⟨l⟩ | ⟨r⟩
  · simp [projectSetToIntersection_inl_mem_iff] at lm1
    simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inl_inl_iff, sumEquivGen_inl_inr_iff]
    rcases lm1 with ⟨lm1, r, lm2, lm3⟩
    exists r
  · simp [projectSetToIntersection_inr_mem_iff] at lm1
    simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inr_iff, sumEquivGen_inr_inl_iff]
    rcases lm1 with ⟨lm1, l, lm2, lm3⟩
    exists l


theorem projectSetToIntersection_subset [IsBiUnique rel] {sus: Set (SumUnion rel)} : projectSetToIntersection sus ⊆ sus := by
  dsimp [Set.subset_def]
  intro su lm1
  cases su using indOfSum
  rename_i s
  rcases s with ⟨l⟩ | ⟨r⟩
  · replace lm1 := projectSetToIntersection_inl_mem_iff.mp lm1
    exact lm1.left
  · replace lm1 := projectSetToIntersection_inr_mem_iff.mp lm1
    exact lm1.left


theorem projectSetToIntersection_mem_iff_exists_eq [IsBiUnique rel] {sus: Set (SumUnion rel)} {su: SumUnion rel}
  : (su ∈ projectSetToIntersection sus) ↔ (su ∈ sus ∧ ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r)) := by
  constructor
  · intro lm1
    refine ⟨?_, ?_⟩
    · revert su
      dsimp [← Set.subset_def]
      exact projectSetToIntersection_subset
    · exact exists_eq_of_forall_projectSetToIntersection_mem su lm1
  · rintro ⟨lm1, l, r, lm2, lm3⟩
    subst lm2
    have lm4 := (sumEquivGen_inl_inr_iff.mp ∘ ofSum_eq_iff_sumEquivGen.mp) lm3
    simp [projectSetToIntersection_inl_mem_iff, lm1]
    exists r
    rw [← lm3]
    exact ⟨lm1, lm4⟩

def IsSubIntersection (sus: Set (SumUnion rel)) : Prop := projectSetToIntersection sus = sus

@[defeq]
theorem isSubIntersection_def {sus: Set (SumUnion rel)} : IsSubIntersection sus = (projectSetToIntersection sus = sus) := rfl

theorem isSubIntersection_iff_forall {sus: Set (SumUnion rel)} : (IsSubIntersection sus) ↔ (∀(su: SumUnion rel), (su ∈ projectSetToIntersection sus) ↔ (su ∈ sus)) := by
  dsimp [isSubIntersection_def]
  rw [Set.ext_iff]

namespace IsSubIntersection

variable {sus: Set (SumUnion rel)}

theorem projectSetToIntersection_eq_self (h: IsSubIntersection sus) : projectSetToIntersection sus = sus := h

theorem projectSetToIntersection_mem_iff_mem (h: IsSubIntersection sus) {su: SumUnion rel} : (su ∈ projectSetToIntersection sus) ↔ (su ∈ sus) := isSubIntersection_iff_forall.mp h su

theorem exists_eq_of_mem [IsBiUnique rel] (h: IsSubIntersection sus) {su: SumUnion rel} (req: su ∈ sus) : ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r) :=
  exists_eq_of_forall_projectSetToIntersection_mem _ (h.projectSetToIntersection_mem_iff_mem.mpr req)

theorem forall_exists_eq_of_mem [IsBiUnique rel] (h: IsSubIntersection sus) (su: SumUnion rel) (req: su ∈ sus) : ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r) :=
  h.exists_eq_of_mem req

theorem exists_eq_and_of_mem [IsBiUnique rel] (h: IsSubIntersection sus) {su: SumUnion rel} (req: su ∈ sus) : ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r) ∧ rel l r := by
  rcases (h.exists_eq_of_mem req) with ⟨l, r, lm1, lm2⟩
  exists l
  exists r
  subst lm1
  simp [lm2]
  exact (sumEquivGen_inl_inr_iff.mp ∘ ofSum_eq_iff_sumEquivGen.mp) lm2

theorem forall_exists_eq_and_of_mem [IsBiUnique rel] (h: IsSubIntersection sus) (su: SumUnion rel) (req: su ∈ sus) : ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r) ∧ rel l r :=
  h.exists_eq_and_of_mem req


theorem exists_rel_of_mem [IsBiUnique rel] (h: IsSubIntersection sus) {su: SumUnion rel} (req: su ∈ sus) : ∃l r, rel l r := by
  rcases (h.exists_eq_and_of_mem req) with ⟨l, r, lm1, lm2, lm3⟩
  exists l
  exists r

theorem forall_exists_rel_of_mem [IsBiUnique rel] (h: IsSubIntersection sus) (su: SumUnion rel) (req: su ∈ sus) : ∃l r, rel l r :=
  h.exists_rel_of_mem req

theorem left_mem_exists_iff_right_mem_exists [IsBiUnique rel] (h: IsSubIntersection sus) : (∃l, (.ofSum (.inl l) ∈ sus)) ↔ (∃r, (.ofSum (.inr r) ∈ sus)) := by
  have lm1 := h.projectSetToIntersection_eq_self
  conv =>
    conv => lhs; rw [← lm1]
    conv => rhs; rw [← lm1]
  simp [projectSetToIntersection_inl_mem_iff, projectSetToIntersection_inr_mem_iff]
  constructor
  · rintro ⟨l, lm2, r, lm3, lm4⟩
    exists r
    refine ⟨lm3, ?_⟩
    exists l
  · rintro ⟨r, lm2, l, lm3, lm4⟩
    exists l
    refine ⟨lm3, ?_⟩
    exists r

theorem right_mem_and_rel_of_left_mem [IsBiUnique rel] (h: IsSubIntersection sus) (l: αl) (req: (.ofSum (.inl l) ∈ sus)) : ∃r, (.ofSum (.inr r) ∈ sus) ∧ rel l r := by
  have lm1 := h.projectSetToIntersection_eq_self
  rewrite [← lm1] at req
  simp [projectSetToIntersection_inl_mem_iff] at req
  exact req.right

theorem left_mem_and_rel_of_right_mem [IsBiUnique rel] (h: IsSubIntersection sus) (r: αr) (req: (.ofSum (.inr r) ∈ sus)) : ∃l, (.ofSum (.inl l) ∈ sus) ∧ rel l r := by
  have lm1 := h.projectSetToIntersection_eq_self
  rewrite [← lm1] at req
  simp [projectSetToIntersection_inr_mem_iff] at req
  exact req.right


theorem forall_mem_rel_exists_of_setOfLeftSet [IsBiUnique rel] {sl: Set αl} (h: IsSubIntersection (setOfLeftSet rel sl)) : ∀l ∈ sl, ∃r ∈ (projectLeftSetToRightSet rel sl), rel l r := by
  intro l lm1
  have lm2 := h.right_mem_and_rel_of_left_mem l
  simp [setOfLeftSet_mem_inl_iff_mem] at lm2
  specialize lm2 lm1
  rcases lm2 with ⟨r, lm2, lm3⟩
  dsimp [projectLeftSetToRightSet_mem_eq_mem]
  exists r


theorem forall_mem_rel_exists_of_setOfRightSet [IsBiUnique rel] {sr: Set αr} (h: IsSubIntersection (setOfRightSet rel sr)) : ∀r ∈ sr, ∃l ∈ (projectRightSetToLeftSet rel sr), rel l r := by
  intro r lm1
  have lm2 := h.left_mem_and_rel_of_right_mem r
  simp [setOfRightSet_mem_inr_iff_mem] at lm2
  specialize lm2 lm1
  rcases lm2 with ⟨l, lm2, lm3⟩
  dsimp [projectRightSetToLeftSet_mem_eq_mem]
  exists l

theorem projectLeftSetToRightSet_injOn_of_rel (rel: αl → αr → Prop) [IsBiUnique rel] : Set.InjOn (projectLeftSetToRightSet rel) { sl: Set αl | IsSubIntersection (setOfLeftSet rel sl) } := by
  intro sl1 lm1 sl2 lm2 lm3
  dsimp at lm1 lm2
  have lm1_1 := lm1.forall_mem_rel_exists_of_setOfLeftSet
  have lm2_1 := lm2.forall_mem_rel_exists_of_setOfLeftSet
  rewrite [Set.ext_iff] at ⊢ lm3
  dsimp [projectLeftSetToRightSet_mem_eq_mem] at lm3 lm1_1 lm2_1
  intro l
  specialize lm1_1 l
  specialize lm2_1 l
  constructor
  · intro lm4
    specialize lm1_1 lm4
    rcases lm1_1 with ⟨r, lm5, lm6⟩
    have lm7 := (lm3 r).mp lm5
    simp [setOfLeftSet_mem_inr_iff_mem] at lm7
    rcases lm7 with ⟨l2, lm7, lm8⟩
    have lm9 := IsBiUnique.leftUnique lm6 lm8
    rw [lm9]
    exact lm7
  · intro lm4
    specialize lm2_1 lm4
    rcases lm2_1 with ⟨r, lm5, lm6⟩
    have lm7 := (lm3 r).mpr lm5
    simp [setOfLeftSet_mem_inr_iff_mem] at lm7
    rcases lm7 with ⟨l2, lm7, lm8⟩
    have lm9 := IsBiUnique.leftUnique lm6 lm8
    rw [lm9]
    exact lm7

theorem projectRightSetToLeftSet_injOn_of_rel (rel: αl → αr → Prop) [IsBiUnique rel] : Set.InjOn (projectRightSetToLeftSet rel) { sr: Set αr | IsSubIntersection (setOfRightSet rel sr) } := by
  intro sr1 lm1 sr2 lm2 lm3
  dsimp at lm1 lm2
  have lm1_1 := lm1.forall_mem_rel_exists_of_setOfRightSet
  have lm2_1 := lm2.forall_mem_rel_exists_of_setOfRightSet
  rewrite [Set.ext_iff] at ⊢ lm3
  dsimp [projectRightSetToLeftSet_mem_eq_mem] at ⊢ lm3 lm1_1 lm2_1
  intro r
  specialize lm1_1 r
  specialize lm2_1 r
  constructor
  · intro lm4
    specialize lm1_1 lm4
    rcases lm1_1 with ⟨l, lm5, lm6⟩
    have lm7 := (lm3 l).mp lm5
    simp [setOfRightSet_mem_inl_iff_mem] at lm7
    rcases lm7 with ⟨r2, lm7, lm8⟩
    have lm9 := IsBiUnique.rightUnique lm6 lm8
    rw [lm9]
    exact lm7
  · intro lm4
    specialize lm2_1 lm4
    rcases lm2_1 with ⟨l, lm5, lm6⟩
    have lm7 := (lm3 l).mpr lm5
    simp [setOfRightSet_mem_inl_iff_mem] at lm7
    rcases lm7 with ⟨l2, lm7, lm8⟩
    have lm9 := IsBiUnique.rightUnique lm6 lm8
    rw [lm9]
    exact lm7



end IsSubIntersection

theorem isSubIntersection_iff_forall_mem_exists_rel [IsBiUnique rel] {sus: Set (SumUnion rel)} : IsSubIntersection sus ↔ (∀su ∈ sus, ∃l r, su = .ofSum (.inl l) ∧ su = .ofSum (.inr r)) := by
  constructor
  · intro lm1 su lm2
    exact lm1.exists_eq_of_mem lm2
  · intro lm1
    refine isSubIntersection_iff_forall.mpr ?_
    intro su
    specialize lm1 su
    simp [projectSetToIntersection_mem_iff_exists_eq]
    intro lm2
    specialize lm1 lm2
    simpa using lm1

theorem isSubIntersection_setOfLeftSet_iff_forall_mem_rel_exists [IsBiUnique rel] {sl: Set αl}
  : IsSubIntersection (setOfLeftSet rel sl) ↔ (∀l ∈ sl, ∃r, rel l r) := by
  constructor
  · intro lm1 l lm2
    have lm3 := lm1.forall_mem_rel_exists_of_setOfLeftSet l lm2
    rcases lm3 with ⟨r, lm3, lm4⟩
    exists r
  · intro lm1
    simp [isSubIntersection_iff_forall_mem_exists_rel]
    intro su lm2
    dsimp [setOfLeftSet] at lm2
    rcases lm2 with ⟨l, lm2, lm3⟩
    subst lm3
    refine ⟨?_, ?_⟩
    · exists l
    · specialize lm1 l lm2
      rcases lm1 with ⟨r, lm1⟩
      exists r
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inl_inr_iff]
      exact lm1

theorem isSubIntersection_setOfRightSet_iff_forall_mem_rel_exists [IsBiUnique rel] {sr: Set αr}
  : IsSubIntersection (setOfRightSet rel sr) ↔ (∀r ∈ sr, ∃l, rel l r) := by
  constructor
  · intro lm1 r lm2
    have lm3 := lm1.forall_mem_rel_exists_of_setOfRightSet r lm2
    rcases lm3 with ⟨l, lm3, lm4⟩
    exists l
  · intro lm1
    simp [isSubIntersection_iff_forall_mem_exists_rel]
    intro su lm2
    dsimp [setOfRightSet] at lm2
    rcases lm2 with ⟨r, lm2, lm3⟩
    subst lm3
    refine ⟨?_, ?_⟩
    · specialize lm1 r lm2
      rcases lm1 with ⟨l, lm1⟩
      exists l
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inl_iff]
      exact lm1
    · exists r

namespace IsSubIntersection

variable {sl: Set αl} {sr: Set αr}

theorem of_projectLeftSetToRightSet_eq [IsBiUnique rel] (req: projectLeftSetToRightSet rel sl = sr) : IsSubIntersection (setOfRightSet rel sr) := by
  rewrite [Set.ext_iff] at req
  simp [projectLeftSetToRightSet_mem_iff] at req
  refine isSubIntersection_setOfRightSet_iff_forall_mem_rel_exists.mpr ?_
  intro r lm1
  rcases (req r).mpr lm1 with ⟨l, lm2, lm3⟩
  exists l

theorem of_projectRightSetToLeftSet_eq [IsBiUnique rel] (req: projectRightSetToLeftSet rel sr = sl) : IsSubIntersection (setOfLeftSet rel sl) := by
  rewrite [Set.ext_iff] at req
  simp [projectRightSetToLeftSet_mem_iff] at req
  refine isSubIntersection_setOfLeftSet_iff_forall_mem_rel_exists.mpr ?_
  intro l lm1
  rcases (req l).mpr lm1 with ⟨r, lm2, lm3⟩
  exists r

end IsSubIntersection


/-
theorem forall_mem_rel_exists_of_setOfLeftSet [IsBiUnique rel] {sl: Set αl} (h: IsSubIntersection (setOfLeftSet rel sl)) : ∀l ∈ sl, ∃r ∈ (projectLeftSetToRightSet rel sl), rel l r := by
  intro l lm1
  have lm2 := h.right_mem_and_rel_of_left_mem l
  simp [setOfLeftSet_mem_inl_iff_mem] at lm2
  specialize lm2 lm1
  rcases lm2 with ⟨r, lm2, lm3⟩
  dsimp [projectLeftSetToRightSet_mem_eq_mem]
  exists r


theorem forall_mem_rel_exists_of_setOfRightSet [IsBiUnique rel] {sr: Set αr} (h: IsSubIntersection (setOfRightSet rel sr)) : ∀r ∈ sr, ∃l ∈ (projectRightSetToLeftSet rel sr), rel l r := by
  intro r lm1
  have lm2 := h.left_mem_and_rel_of_right_mem r
  simp [setOfRightSet_mem_inr_iff_mem] at lm2
  specialize lm2 lm1
  rcases lm2 with ⟨l, lm2, lm3⟩
  dsimp [projectRightSetToLeftSet_mem_eq_mem]
  exists l
-/


def SetHEq (rel: αl → αr → Prop) (sl: Set αl) (sr: Set αr) : Prop := setOfLeftSet rel sl = setOfRightSet rel sr

section SetHEqSection

variable {sl: Set αl} {sr: Set αr}

@[defeq]
theorem setHEq_def : SetHEq rel sl sr = (setOfLeftSet rel sl = setOfRightSet rel sr) := rfl

namespace SetHEq


theorem isSubIntersection_left [IsBiUnique rel] (h: SetHEq rel sl sr) : IsSubIntersection (setOfLeftSet rel sl) := by
  dsimp [setHEq_def] at h
  dsimp [isSubIntersection_def]
  refine Set.ext ?_
  intro su
  simp [projectSetToIntersection_mem_iff_exists_eq]
  intro lm1
  cases su using indOfSum
  rename_i s
  rcases s with ⟨l⟩ | ⟨r⟩
  · refine ⟨?_, ?_⟩
    · exists l
    · rewrite [h] at lm1
      simp [setOfRightSet_mem_inl_iff_mem] at lm1
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inl_inr_iff]
      rcases lm1 with ⟨r, _, _⟩
      exists r
  · refine ⟨?_, ?_⟩
    · simp [setOfLeftSet_mem_inr_iff_mem] at lm1
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inl_iff]
      rcases lm1 with ⟨l, _, _⟩
      exists l
    · exists r

theorem isSubIntersection_right [IsBiUnique rel] (h: SetHEq rel sl sr) : IsSubIntersection (setOfRightSet rel sr) :=
  (congrArg IsSubIntersection h).mp (h.isSubIntersection_left)

theorem of_isSubIntersection_left [IsBiUnique rel] (req: IsSubIntersection (setOfLeftSet rel sl)) : SetHEq rel sl (projectLeftSetToRightSet rel sl) := by
  dsimp [setHEq_def]
  rw [← req.projectSetToIntersection_eq_self]
  refine Set.ext ?_
  intro su
  simp [projectSetToIntersection, projectLeftSetToRightSet, projectSetToLeftSet_setOfLeftSet_leftInverse.eq]
  revert su
  dsimp [← Set.subset_def]
  exact projectSetToRightSet_setOfRightSet_subset

theorem of_isSubIntersection_right [IsBiUnique rel] (req: IsSubIntersection (setOfRightSet rel sr)) : SetHEq rel (projectRightSetToLeftSet rel sr) sr := by
  dsimp [setHEq_def]
  rw [← req.projectSetToIntersection_eq_self]
  refine Set.ext ?_
  intro su
  simp [projectSetToIntersection, projectRightSetToLeftSet, projectSetToRightSet_setOfRightSet_leftInverse.eq]
  revert su
  dsimp [← Set.subset_def]
  exact projectSetToLeftSet_setOfLeftSet_subset

theorem projectLeftSetToRightSet_eq [IsBiUnique rel] (h: SetHEq rel sl sr) : projectLeftSetToRightSet rel sl = sr := by
  dsimp [setHEq_def] at h
  dsimp [projectLeftSetToRightSet]
  rw [h]
  exact projectSetToRightSet_setOfRightSet_leftInverse.eq _

theorem projectRightSetToLeftSet_eq [IsBiUnique rel] (h: SetHEq rel sl sr) : projectRightSetToLeftSet rel sr = sl := by
  dsimp [setHEq_def] at h
  dsimp [projectRightSetToLeftSet]
  rw [← h]
  exact projectSetToLeftSet_setOfLeftSet_leftInverse.eq _


end SetHEq

theorem isSubIntersection_left_iff_setHEq [IsBiUnique rel] : IsSubIntersection (setOfLeftSet rel sl) ↔ SetHEq rel sl (projectLeftSetToRightSet rel sl) := by
  constructor
  · intro lm1
    exact SetHEq.of_isSubIntersection_left lm1
  · intro lm1
    exact lm1.isSubIntersection_left

theorem isSubIntersection_right_iff_setHEq [IsBiUnique rel] : IsSubIntersection (setOfRightSet rel sr) ↔ SetHEq rel (projectRightSetToLeftSet rel sr) sr := by
  constructor
  · intro lm1
    exact SetHEq.of_isSubIntersection_right lm1
  · intro lm1
    exact lm1.isSubIntersection_right

namespace SetHEq


theorem leftUnique_of_rel (rel: αl → αr → Prop) [IsBiUnique rel] : Relator.LeftUnique (SetHEq rel) := by
  intro sl1 sl2 sr lm1 lm2
  have lm3 := lm1.projectLeftSetToRightSet_eq.trans lm2.projectLeftSetToRightSet_eq.symm
  have lm4 := IsSubIntersection.projectLeftSetToRightSet_injOn_of_rel rel lm1.isSubIntersection_left lm2.isSubIntersection_left
  exact lm4 lm3

theorem rightUnique_of_rel (rel: αl → αr → Prop) [IsBiUnique rel] : Relator.RightUnique (SetHEq rel) := by
  intro sl sr1 sr2 lm1 lm2
  have lm3 := lm1.projectRightSetToLeftSet_eq.trans lm2.projectRightSetToLeftSet_eq.symm
  have lm4 := IsSubIntersection.projectRightSetToLeftSet_injOn_of_rel rel lm1.isSubIntersection_right lm2.isSubIntersection_right
  exact lm4 lm3

end SetHEq

theorem setHEq_iff_eq_and_eq [IsBiUnique rel] : (SetHEq rel sl sr) ↔ (projectLeftSetToRightSet rel sl = sr ∧ projectRightSetToLeftSet rel sr = sl) := by
  constructor
  · intro lm1
    refine ⟨?_, ?_⟩
    · exact lm1.projectLeftSetToRightSet_eq
    · exact lm1.projectRightSetToLeftSet_eq
  · rintro ⟨lm1, lm2⟩
    have lm3 := IsSubIntersection.of_projectLeftSetToRightSet_eq lm1
    have lm4 := SetHEq.of_isSubIntersection_right lm3
    rewrite [lm2] at lm4
    exact lm4

theorem setHEq_iff_forall_iff : (SetHEq rel sl sr) ↔ (∀(su: SumUnion rel), (∃l ∈ sl, su = .ofSum (.inl l)) ↔ (∃r ∈ sr, su = .ofSum (.inr r))) := by
  dsimp [setHEq_def]
  rw [Set.ext_iff]
  dsimp [setOfLeftSet, setOfRightSet]
  rfl

theorem setHEq_iff_forall_iff_and_forall_iff [IsBiUnique rel] : (SetHEq rel sl sr) ↔ ((∀l, ((l ∈ sl) ↔ (∃r ∈ sr, rel l r))) ∧ (∀r, ((r ∈ sr) ↔ (∃l ∈ sl, rel l r)))) := by
  rw [setHEq_iff_forall_iff]
  constructor
  · intro lm1
    refine ⟨?_, ?_⟩
    · intro l
      specialize lm1 (.ofSum (.inl l))
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inl_inl_iff, sumEquivGen_inl_inr_iff] at lm1
      exact lm1
    · intro r
      specialize lm1 (.ofSum (.inr r))
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inl_iff, sumEquivGen_inr_inr_iff] at lm1
      exact lm1.symm
  · rintro ⟨lm1, lm2⟩
    intro su
    cases su using indInlInrOfSum
    · rename_i l
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inl_inl_iff, sumEquivGen_inl_inr_iff]
      exact lm1 l
    · rename_i r
      simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inl_iff, sumEquivGen_inr_inr_iff]
      exact (lm2 r).symm

--∀l r, (rel l r) ↔ (l ∈ sl ↔ r ∈ sr)

namespace SetHEq


theorem mem_iff_mem_of_rel [IsBiUnique rel] (h: SetHEq rel sl sr) l r (req: rel l r) : l ∈ sl ↔ r ∈ sr := by
  simp [setHEq_iff_forall_iff_and_forall_iff] at h
  rcases h with ⟨lm1, lm2⟩
  specialize lm1 l
  specialize lm2 r
  constructor
  · intro lm4
    simp [lm4] at lm1
    rcases lm1 with ⟨r2, lm5, lm6⟩
    have lm7 := IsBiUnique.rightUnique req lm6
    subst lm7
    exact lm5
  · intro lm4
    simp [lm4] at lm2
    rcases lm2 with ⟨l2, lm5, lm6⟩
    have lm7 := IsBiUnique.leftUnique req lm6
    subst lm7
    exact lm5

theorem not_mem_iff_not_mem_of_rel [IsBiUnique rel] (h: SetHEq rel sl sr) l r (req: rel l r) : (l ∉ sl) ↔ (r ∉ sr) := by
  have lm1 := h.mem_iff_mem_of_rel l r req
  simpa only [not_iff_not] using lm1


theorem of_mem_iff_mem_of_rel₂ [IsBiUnique rel]
  (req1: ∀l, ∃r, (rel l r) ∧ (l ∈ sl ↔ r ∈ sr))
  (req2: ∀r, ∃l, (rel l r) ∧ (l ∈ sl ↔ r ∈ sr)) : SetHEq rel sl sr := by
  simp [setHEq_iff_forall_iff]
  intro su
  cases su using indInlInrOfSum with
  | inl l =>
    simp [sum_simp]
    rcases (req1 l) with ⟨r, lm1, lm2⟩
    constructor
    · intro lm3
      replace lm2 := lm2.mp lm3
      exists r
    · rintro ⟨r2, lm3, lm4⟩
      have lm5 := IsBiUnique.rightUnique lm1 lm4
      subst lm5
      exact lm2.mpr lm3
  | inr r =>
    simp [sum_simp]
    constructor
    · rintro ⟨l, lm1, lm2⟩
      rcases (req1 l) with ⟨r2, lm3, lm4⟩
      have lm5 := IsBiUnique.rightUnique lm2 lm3
      subst lm5
      exact lm4.mp lm1
    · intro lm1
      rcases (req2 r) with ⟨l, lm2, lm3⟩
      replace lm3 := lm3.mpr lm1
      exists l

--(∀(su: SumUnion rel), (∃l ∈ sl, su = .ofSum (.inl l)) ↔ (∃r ∈ sr, su = .ofSum (.inr r)))

theorem forall_sumUnion_exists_iff_exists (h: SetHEq rel sl sr) (su: SumUnion rel) : (∃l ∈ sl, su = .ofSum (.inl l)) ↔ (∃r ∈ sr, su = .ofSum (.inr r)) :=
  setHEq_iff_forall_iff.mp h su


theorem forall_left_mem_iff_right_mem_and_rel_exists [IsBiUnique rel] (h: SetHEq rel sl sr) (l: αl) : (l ∈ sl) ↔ (∃r ∈ sr, rel l r) := by
  have lm1 := setHEq_iff_forall_iff_and_forall_iff.mp h
  exact (lm1.left l)

theorem forall_right_mem_iff_left_mem_and_rel_exists [IsBiUnique rel] (h: SetHEq rel sl sr) (r: αr) : (r ∈ sr) ↔ (∃l ∈ sl, rel l r) := by
  have lm1 := setHEq_iff_forall_iff_and_forall_iff.mp h
  exact (lm1.right r)

/-
theorem forall_left_mem_iff_rel_exists [IsBiUnique rel] (h: SetHEq rel sl sr) (l: αl) : (l ∈ sl) ↔ (∃r, rel l r) := by
  constructor
  · intro lm1
    rcases (h.forall_left_right_mem_and_rel_exists_iff_mem l).mpr lm1 with ⟨r, lm2, lm3⟩
    exists r
  · rintro ⟨r, lm1⟩
    have lm2 := h.mem_iff_mem_of_rel l r lm1
    rewrite [iff_iff_and_or_not_and_not] at lm2
-/
/-
    refine (h.forall_left_right_mem_and_rel_exists_iff_mem l).mp ?_
    have lm2 := h.forall_sumUnion_exists_iff_exists (.ofSum (.inl l))
    simp [sum_simp] at lm2
-/
    --have lm2 := h.mem_iff_mem_of_rel l r lm1

  --have lm1 := h.forall_left_mem_iff_right_mem_and_rel_exists l
  --rcases lm1 with ⟨lm1, lm2⟩
  --simp at lm1 lm2

end SetHEq


/-
theorem setHEq_iff_rel_iff_iff [IsBiUnique rel] : (SetHEq rel sl sr) ↔ (∀l r, (rel l r) ↔ (l ∈ sl ↔ r ∈ sr)) := by
  constructor
  · intro lm1 l r
    constructor
    · simp [setHEq_iff_forall_iff_and_forall_iff] at lm1
      rcases lm1 with ⟨lm1, lm2⟩
      specialize lm1 l
      specialize lm2 r
      intro lm3
      constructor
      · intro lm4
        simp [lm4] at lm1
        rcases lm1 with ⟨r2, lm5, lm6⟩
        have lm7 := IsBiUnique.rightUnique lm3 lm6
        subst lm7
        exact lm5
      · intro lm4
        simp [lm4] at lm2
        rcases lm2 with ⟨l2, lm5, lm6⟩
        have lm7 := IsBiUnique.leftUnique lm3 lm6
        subst lm7
        exact lm5
    · simp [setHEq_iff_forall_iff_and_forall_iff] at lm1
      rcases lm1 with ⟨lm1, lm2⟩
      intro lm3
      simp [iff_iff_and_or_not_and_not] at lm3
-/
/-
      specialize lm1 l
      specialize lm2 r
      rcases lm1 with ⟨lm1, lm4⟩
      rcases lm2 with ⟨lm2, lm5⟩
      --simp [lm3] at lm1 lm4
      by_contra lm6
      by_cases lm7: r ∈ sr
      ·
-/
/-
      simp [setHEq_iff_forall_iff] at lm1
      have lm3 := lm1 (.ofSum (.inl l))
      simp [sum_simp, lm2] at lm3
      rcases lm3 with ⟨lm4, lm5⟩
      simp at lm4 lm5
-/
/-
  · intro lm1
    refine ⟨?_, ?_⟩
    · intro l
      specialize lm1 l
      simp []
-/

end SetHEqSection


end SumUnion



end Nemonuri.Relations.Heterogeneous

end
