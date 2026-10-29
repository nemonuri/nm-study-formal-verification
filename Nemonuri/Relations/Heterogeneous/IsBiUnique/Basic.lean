module

public import Mathlib.Logic.Relator
public import Mathlib.Data.Fintype.Basic


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

theorem left_pred_iff_exists_left_pred_and_rel_of_rel (pred: αl → Prop) {l: αl} {r: αr} (req: rel l r) : (∃l, pred l ∧ rel l r) ↔ (pred l) := by
  constructor
  · rintro ⟨l2, lm1, lm2⟩
    have lm3 := IsBiUnique.leftUnique req lm2
    subst lm3
    exact lm1
  · intro lm1
    exists l

theorem right_pred_iff_exists_left_pred_and_rel_of_rel (pred: αr → Prop) {l: αl} {r: αr} (req: rel l r) : (∃r, pred r ∧ rel l r) ↔ (pred r) := by
  constructor
  · rintro ⟨r2, lm1, lm2⟩
    have lm3 := IsBiUnique.rightUnique req lm2
    subst lm3
    exact lm1
  · intro lm1
    exists r


section Find

variable {αl αr: Type*}

def findRightOfList? (rel: αl → αr → Prop) [IsBiUnique rel] [DecidableRel rel] (rs: List αr) (l: αl) : Option αr :=
  rs.find? (fun r => decide (rel l r))

def findLeftOfList? (rel: αl → αr → Prop) [IsBiUnique rel] [DecidableRel rel] (ls: List αl) (r: αr) : Option αl :=
  ls.find? (fun l => decide (rel l r))

def findRight? (rel: αl → αr → Prop) [IsBiUnique rel] [DecidableRel rel] (rs: Multiset αr) (l: αl) : Option αr :=
  rs.liftOn (findRightOfList? rel · l) (by
    intro rs1 rs2 lm1
    change List.Perm rs1 rs2 at lm1
    induction lm1 with
    | nil => rfl
    | cons r _ lm1 =>
      by_cases lm3: rel l r
      · simp [findRightOfList?, lm3]
      · simp [findRightOfList?, lm3]
        dsimp [findRightOfList?] at lm1
        exact lm1
    | swap r1 r2 _ =>
      by_cases lm1: rel l r1
      <;> by_cases lm2: rel l r2
      <;> (simp [lm1, lm2, findRightOfList?])
      · exact IsBiUnique.rightUnique lm2 lm1
    | trans _ _ lm1 lm2 =>
      exact lm1.trans lm2 )

def findLeft? (rel: αl → αr → Prop) [IsBiUnique rel] [DecidableRel rel] (ls: Multiset αl) (r: αr) : Option αl :=
  ls.liftOn (findLeftOfList? rel · r) (by
    intro ls1 ls2 lm1
    change List.Perm ls1 ls2 at lm1
    induction lm1 with
    | nil => rfl
    | cons l _ lm1 =>
      by_cases lm3: rel l r
      · simp [findLeftOfList?, lm3]
      · simp [findLeftOfList?, lm3]
        dsimp [findLeftOfList?] at lm1
        exact lm1
    | swap l1 l2 _ =>
      by_cases lm1: rel l1 r
      <;> by_cases lm2: rel l2 r
      <;> (simp [lm1, lm2, findLeftOfList?])
      · exact IsBiUnique.leftUnique lm2 lm1
    | trans _ _ lm1 lm2 =>
      exact lm1.trans lm2 )

variable {rel: αl → αr → Prop} [IsBiUnique rel] [DecidableRel rel]

theorem findRightOfList?_nil {l: αl} : findRightOfList? rel [] l = .none := by simp [findRightOfList?]

theorem findLeftOfList?_nil {r: αr} : findLeftOfList? rel [] r = .none := by simp [findLeftOfList?]

theorem findRightOfList?_cons {l: αl} {r: αr} {rs: List αr} : findRightOfList? rel (r :: rs) l = if rel l r then .some r else findRightOfList? rel rs l := by
  by_cases lm1: rel l r <;> simp [lm1, findRightOfList?]

theorem findLeftOfList?_cons {l: αl} {ls: List αl} {r: αr} : findLeftOfList? rel (l :: ls) r = if rel l r then .some l else findLeftOfList? rel ls r := by
  by_cases lm1: rel l r <;> simp [lm1, findLeftOfList?]


theorem findRight?_eq_some_iff {rs: Multiset αr} {l: αl} {r: αr} : (findRight? rel rs l = .some r) ↔ (r ∈ rs ∧ rel l r) := by
  cases rs using Quotient.ind
  rename_i rs
  dsimp only [findRight?, Quotient.liftOn_mk]
  simp
  induction rs with
  | nil => simp [findRightOfList?]
  | cons r2 rs lm1 =>
    simp only [findRightOfList?_cons]
    by_cases lm2: rel l r2
    · simp [lm2]
      constructor
      · intro lm3
        subst lm3
        simpa using lm2
      · rintro ⟨_, lm3⟩
        exact IsBiUnique.rightUnique lm2 lm3
    · simp [lm2, lm1]
      intro lm3 lm4
      subst lm4
      contradiction

theorem findLeft?_eq_some_iff {ls: Multiset αl} {l: αl} {r: αr} : (findLeft? rel ls r = .some l) ↔ (l ∈ ls ∧ rel l r) := by
  cases ls using Quotient.ind
  rename_i ls
  dsimp only [findLeft?, Quotient.liftOn_mk]
  simp
  induction ls with
  | nil => simp [findLeftOfList?]
  | cons l2 ls lm1 =>
    simp only [findLeftOfList?_cons]
    by_cases lm2: rel l2 r
    · simp [lm2]
      constructor
      · intro lm3
        subst lm3
        simpa using lm2
      · rintro ⟨_, lm3⟩
        exact IsBiUnique.leftUnique lm2 lm3
    · simp [lm2, lm1]
      intro lm3 lm4
      subst lm4
      contradiction



end Find


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

protected def refl (α: Type*) [DecidableEq α] : BiUniqueIndicator α α where
  indicate l r := decide (l = r)
  valid := by simp [Relator.BiUnique, Relator.LeftUnique, Relator.RightUnique]

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


theorem right?_isSome_true_iff (h: IsPartialCongruence pcs rel) {l: αl} : ((pcs.right? l).isSome = .true) ↔ ∃r, rel l r := by
  rw [Option.isSome_iff_exists]
  simp [h.right?_eq_some_iff_rel]

theorem left?_isSome_true_iff (h: IsPartialCongruence pcs rel) {r: αr} : ((pcs.left? r).isSome = .true) ↔ ∃l, rel l r := by
  rw [Option.isSome_iff_exists]
  simp [h.left?_eq_some_iff_rel]

def right (h: IsPartialCongruence pcs rel) (l: αl) (req: ∃r, rel l r) : αr := (pcs.right? l).get (h.right?_isSome_true_iff.mpr req)

def left (h: IsPartialCongruence pcs rel) (r: αr) (req: ∃l, rel l r) : αl := (pcs.left? r).get (h.left?_isSome_true_iff.mpr req)

theorem right?_eq_right_some (h: IsPartialCongruence pcs rel) {l: αl} (req: ∃r, rel l r) : pcs.right? l = .some (h.right l req) := by
  simp [right]

theorem left?_eq_left_some (h: IsPartialCongruence pcs rel) {r: αr} (req: ∃l, rel l r) : pcs.left? r = .some (h.left r req) := by
  simp [left]

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


def ofFintype (rel: αl → αr → Prop) [DecidableRel rel] [Fintype αl] [Fintype αr] [IsBiUnique rel] : PartialCongruence rel where
  right? := IsBiUnique.findRight? rel Finset.univ.val
  left? := IsBiUnique.findLeft? rel Finset.univ.val
  valid := by
    refine .mk ?_ ?_ <;> (dsimp; intro l r)
    · simp [IsBiUnique.findRight?_eq_some_iff]
    · simp [IsBiUnique.findLeft?_eq_some_iff]

def ofBiUniqueIndicatorRefl (α: Type*) [DecidableEq α] : PartialCongruence (BiUniqueIndicator.refl α).Rel where
  right? x := .some x
  left? x := .some x
  valid := by
    refine .mk ?_ ?_ <;> (
      dsimp [BiUniqueIndicator.rel_def, BiUniqueIndicator.refl]
      intro l r
      simp )
    · exact Eq.comm

end PartialCongruence



end Nemonuri.Relations.Heterogeneous

end
