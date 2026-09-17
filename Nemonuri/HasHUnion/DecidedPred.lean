module

public import Mathlib.Logic.IsEmpty.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri



namespace DecidedProp

inductive Indexed (p: Prop) : Bool → Prop where
  | of_proof (req: p) : Indexed p .true
  | of_disproof (req: ¬p) : Indexed p .false

namespace Indexed

variable {p: Prop}

theorem to_proof (h: Indexed p .true) : p := by cases h; assumption

@[simp]
theorem to_proof_iff : (Indexed p .true) ↔ p := ⟨fun h => h.to_proof, fun h => of_proof h⟩


theorem to_disproof (h: Indexed p .false) : ¬p := by cases h; assumption

@[simp]
theorem to_disproof_iff : (Indexed p .false) ↔ (¬p) := ⟨fun h => h.to_disproof, fun h => of_disproof h⟩

end Indexed

end DecidedProp


namespace DecidedPred

inductive Indexed (α: Type*) (pred: α → Prop) : Bool → Type _ where
  | ofTrue (val: α) (property: pred val) : Indexed α pred .true
  | ofFalse (val: α) (property: ¬(pred val)) : Indexed α pred .false

namespace Indexed

variable {α: Type*} {pred: α → Prop} {b: Bool}

def val: Indexed α pred b → α
  | .ofTrue val _ => val
  | .ofFalse val _ => val

def property (idx: Indexed α pred b) : DecidedProp.Indexed (pred idx.val) b := --
  match idx with
  | .ofTrue _ p => .of_proof p --|> Iff.mp (by simp; exact p)
  | .ofFalse _ p => .of_disproof p --|> Iff.mp (by simp [Indexed.val])

@[simp]
theorem val_ofTrue_eq_self (idx: Indexed α pred .true) : Indexed.ofTrue idx.val idx.property.to_proof = idx := by cases idx; dsimp [val]

@[simp]
theorem val_ofFalse_eq_self (idx: Indexed α pred .false) : Indexed.ofFalse idx.val idx.property.to_disproof = idx := by cases idx; dsimp [val]


def toSubtype (idx: Indexed α pred b) : { val: α // DecidedProp.Indexed (pred val) b } := ⟨idx.val, idx.property⟩

end Indexed

/-
def Filtered (α: Type*) (pred: α → Prop) : Type _ := Option (Indexed α pred .true)

@[defeq]
theorem filtered_def {α: Type _} {pred: α → Prop} : Filtered α pred = Option (Indexed α pred .true) := rfl

namespace Filtered

variable {α: Type*} {pred: α → Prop}


def ofTrue (val: α) (property: pred val) : Filtered α pred := (Option.some (Indexed.ofTrue val property))

def ofFalse (val: α) (_: ¬(pred val)) : Filtered α pred := Option.none

def ofEmpty (_: IsEmpty α) : Filtered α pred := Option.none

def isTrue (fil: Filtered α pred) : Bool := Option.isSome fil

@[defeq]
theorem isTrue_def {fil: Filtered α pred} : fil.isTrue = Option.isSome fil := rfl

def toIndexed (fil: Filtered α pred) (req: fil.isTrue = .true) : Indexed α pred .true := Option.get fil (isTrue_def ▸ req)

@[defeq]
theorem toIndexed_def {fil: Filtered α pred} {req: fil.isTrue = .true} : fil.toIndexed req = Option.get fil (isTrue_def ▸ req) := rfl
-/

/-
theorem ind
  {motive: Filtered α pred → Prop}
  (ofTrue: (val: α) → (property: pred val) → motive (.ofTrue val property))
  (ofFalse: (val: α) → (property: ¬(pred val)) → motive (.ofFalse val property))
  (ofEmpty: (req: IsEmpty α) → motive (.ofEmpty req))
  (t: Filtered α pred)
  : motive t := by
  by_cases lm1: t.isTrue = .true
  · clear ofFalse ofEmpty
    let idx := t.toIndexed lm1
    specialize ofTrue idx.val idx.property
    refine Eq.ndrec ofTrue ?_
    clear ofTrue
    subst idx
    dsimp [isTrue_def] at lm1
    obtain ⟨idx, lm2⟩ := Option.isSome_iff_exists.mp lm1
    subst lm2
    dsimp [Filtered.ofTrue]
    congr
    dsimp [toIndexed_def]
    rcases idx
    dsimp [Indexed.val]
  · clear ofTrue
    dsimp [isTrue_def] at lm1
    simp at lm1
    subst lm1
    --dsimp [Filtered.ofTrue] at ofTrue
-/
/-
  dsimp [filtered_def] at t
  dsimp [Filtered.ofTrue] at ofTrue
  dsimp [Filtered.ofFalse] at ofFalse ofEmpty
  by_cases lm1: Nonempty α
  · clear ofEmpty
    rcases lm1 with ⟨val⟩
    specialize ofTrue val
    specialize ofFalse val
-/
/-
  rcases t with _ | ⟨ind⟩
  · by_cases lm1: Nonempty α
    · clear ofEmpty
      rcases lm1 with ⟨val⟩

-/
/-
      specialize ofTrue val
      specialize ofFalse val
      by_cases lm2: pred val
      ·
-/


/-
end Filtered
-/


end DecidedPred

structure DecidedPred (α: Type _) (pred: α → Prop) where
  isTrue: Bool
  indexed: DecidedPred.Indexed α pred isTrue

namespace DecidedPred

variable {α: Type*} {pred: α → Prop}

@[match_pattern]
def ofTrue (val: α) (req: pred val) : DecidedPred α pred := .mk .true (.ofTrue val req)

@[match_pattern]
def ofFalse (val: α) (req: ¬(pred val)) : DecidedPred α pred := .mk .false (.ofFalse val req)

@[elab_as_elim]
def recOnTrueFalse.{u}
  {motive: DecidedPred α pred → Sort u}
  (ofTrue: (val: α) → (req: pred val) → motive (.ofTrue val req))
  (ofFalse: (val: α) → (req: ¬(pred val)) → motive (.ofFalse val req))
  (t: DecidedPred α pred)
  : motive t :=
  match t with
  | .ofTrue val lm1 => ofTrue val lm1
  | .ofFalse val lm1 => ofFalse val lm1

def val (dp: DecidedPred α pred) : α := dp.indexed.val

def toSubtypeSum : DecidedPred α pred → { x // pred x } ⊕ { x // ¬pred x }
  | .mk .true idx => Sum.inl ⟨idx.val, idx.property.to_proof⟩
  | .mk .false idx => Sum.inr ⟨idx.val, idx.property.to_disproof⟩

def ofSubtypeSum : { x // pred x } ⊕ { x // ¬pred x } → DecidedPred α pred
  | .inl ⟨val, lm1⟩ => .ofTrue val lm1
  | .inr ⟨val, lm1⟩ => .ofFalse val lm1

theorem ofSubtypeSum_toSubtypeSum_left_inverse : Function.LeftInverse (ofSubtypeSum) (@toSubtypeSum α pred) := by
  rintro ⟨b, idx⟩
  rcases b <;> (
    dsimp [ofSubtypeSum, toSubtypeSum, ofTrue, ofFalse]
    simp )

theorem ofSubtypeSum_toSubtypeSum_right_inverse : Function.RightInverse (ofSubtypeSum) (@toSubtypeSum α pred) := by
  intro x
  rcases x with x | x <;> (dsimp [ofSubtypeSum, toSubtypeSum, Indexed.val, ofTrue, ofFalse])

def pure (val: α) [Decidable (pred val)] : DecidedPred α pred := if lm1: pred val then .ofTrue val lm1 else .ofFalse val lm1

def bind (dp: DecidedPred α pred) (f: α → DecidedPred α pred) : DecidedPred α pred := f dp.val

theorem nonempty_iff : (Nonempty (DecidedPred α pred)) ↔ Nonempty α := by
  constructor
  · rintro ⟨dp⟩
    exact .intro dp.val
  · rintro ⟨val⟩
    by_cases lm1: pred val
    · exact .intro (.ofTrue val lm1)
    · exact .intro (.ofFalse val lm1)

theorem isEmpty_iff : (IsEmpty (DecidedPred α pred)) ↔ (IsEmpty α) := by
  rw [← not_iff_not]
  simp
  exact nonempty_iff





def Filtered (α: Type*) (pred: α → Prop) : Type _ := Option (Indexed α pred .true)

@[defeq]
theorem filtered_def {α pred} : Filtered α pred = Option (Indexed α pred .true) := rfl


namespace Filtered


def ofEmpty [IsEmpty α] : Filtered α pred := Option.none

def ofDecided : DecidedPred α pred → Filtered α pred
  | .ofTrue val lm1 => Option.some (.ofTrue val lm1)
  | .ofFalse _ _ => Option.none

/-
theorem inductionOn
  {motive: Filtered α pred → Prop}
  (ofEmpty: (req: IsEmpty α) → motive (.ofEmpty))
  (ofDecided: (dp: DecidedPred α pred) → motive (.ofDecided dp))
  (t: Filtered α pred)
  : motive t := by
  rcases isEmpty_or_nonempty α with lm1 | lm1
  · specialize ofEmpty lm1
    refine Eq.ndrec ofEmpty ?_
    dsimp [Filtered.ofEmpty]
    dsimp [Filtered] at t
    rcases t with _ | t
    · rfl
    · exact lm1.elim t.val
  · clear ofEmpty
    dsimp [filtered_def] at t
    rcases t with _ | t
    · have lm2: Nonempty (DecidedPred α pred) := DecidedPred.nonempty_iff.mpr lm1
      --dsimp [Filtered.ofDecided] at ofDecided
      rcases lm2 with ⟨dp⟩
      specialize ofDecided dp
      dsimp [Filtered.ofDecided] at ofDecided
      split at ofDecided
-/
      --cases dp using recOnTrueFalse
      --specialize ofDecided (.ofFalse )



end Filtered


end DecidedPred

inductive AreFilterEquiv (α: Type*) (filter: α → Prop) (a1 a2: α) : Prop where
  | true (req1: filter a1) (req2: filter a2) (req3: a1 = a2)
  | false (req1: ¬filter a1) (req2: ¬filter a2)

namespace AreFilterEquiv

variable {α: Type*} {filter: α → Prop}

protected instance refl : Std.Refl (AreFilterEquiv α filter) where
  refl x := by
    by_cases lm1: filter x
    · exact .true lm1 lm1 rfl
    · exact .false lm1 lm1

protected instance symm : Std.Symm (AreFilterEquiv α filter) where
  symm x1 x2 := by
    intro lm1
    rcases lm1 with ⟨lm1, lm2, lm3⟩ | ⟨lm1, lm2⟩
    · subst lm3
      exact AreFilterEquiv.refl.refl _
    · exact .false lm2 lm1

protected instance trans : IsTrans _ (AreFilterEquiv α filter) where
  trans x1 x2 x3 req1 req2 := by
    rcases req1 with ⟨lm1, lm2, lm3⟩ | ⟨lm1, lm2⟩
    · subst lm3
      exact req2
    · rcases req2 with ⟨lm3, lm4, lm5⟩ | ⟨lm3, lm4⟩
      · contradiction
      · exact .false lm1 lm4

protected instance equiv : IsEquiv _ (AreFilterEquiv α filter) :=
  let _ : IsPreorder _ (AreFilterEquiv α filter) := .mk
  .mk

theorem equivalence : Equivalence (AreFilterEquiv α filter) := .of_isEquiv (AreFilterEquiv α filter)

@[reducible]
def setoidOfFilter (filter: α → Prop) : Setoid α where
  r := AreFilterEquiv α filter
  iseqv := AreFilterEquiv.equivalence

end AreFilterEquiv

def Filtered {α: Type*} (filter: α → Prop) : Type _ := Quotient (AreFilterEquiv.setoidOfFilter filter)

namespace Filtered

variable {α: Type*} {filter: α → Prop}

def mk (x: α) : Filtered filter := Quotient.mk _ x

@[elab_as_elim]
theorem inductionOn
  {motive: Filtered filter → Prop}
  (mk: (x: α) → motive (.mk x))
  (t: Filtered filter)
  : motive t := by
  cases t using Quotient.inductionOn
  rename_i x
  exact mk x

theorem mk_eq_iff {x1 x2: α} : ((mk x1: Filtered filter) = mk x2) ↔ (AreFilterEquiv _ filter x1 x2) := by
  constructor
  · intro lm1
    exact Quotient.exact lm1
  · intro lm1
    exact Quotient.sound lm1


def liftOn {β: Type*} (fil: Filtered filter) (f: α → β)
           (req: ∀(x1 x2: α), (AreFilterEquiv _ filter x1 x2) → f x1 = f x2) : β :=
    Quotient.liftOn fil f req


theorem mk_eq_iff_of_true {x1 x2: α} (req1: filter x1) (req2: filter x2)
  : ((mk x1: Filtered filter) = mk x2) ↔ (x1 = x2) := by
  rw [mk_eq_iff]
  constructor
  · intro lm1
    rcases lm1
    · assumption
    · contradiction
  · intro lm1
    subst lm1
    exact AreFilterEquiv.equivalence.refl _

theorem mk_eq_of_false {x1 x2: α} (req1: ¬filter x1) (req2: ¬filter x2)
  : (mk x1: Filtered filter) = mk x2 := by
  rw [mk_eq_iff]
  exact .false req1 req2

theorem mk_ne_of_not_iff {x1 x2: α} (req: ¬(filter x1 ↔ filter x2))
  : (mk x1: Filtered filter) ≠ mk x2 := by
  intro lm1
  revert req
  simp
  rw [mk_eq_iff] at lm1
  rcases lm1 with ⟨_,_,lm1⟩ | ⟨lm1, lm2⟩
  · subst lm1; rfl
  · simp [lm1, lm2]


def ofTrue (x: α) (_: filter x) : Filtered filter := mk x

def ofFalse (x: α) (_: ¬filter x) : Filtered filter := mk x

def val? [DecidablePred filter] (fil: Filtered filter) : Option α :=
  let aux (x: α) : Option α := if filter x then some x else none
  Filtered.liftOn fil aux (by
    intro x1 x2 lm1
    subst aux
    dsimp
    rcases lm1 with ⟨_,_,lm1⟩ | ⟨lm1, lm2⟩
    · subst lm1
      rfl
    · simp [lm1, lm2] )

theorem true_of_val_mem [DecidablePred filter] {fil: Filtered filter} (x: α) (req: x ∈ fil.val?) : filter x := by
  simp at req
  cases fil using inductionOn
  rename_i x2
  dsimp [val?] at req
  simp [Filtered.mk, Filtered.liftOn] at req
  simp [Quotient.liftOn, Quotient.mk] at req
  rcases req with ⟨lm1, lm2⟩
  subst lm2
  exact lm1





/-
def recOnTrueFalse.{u}
  {motive: Filtered filter → Sort u}
  (ofTrue: (x: α) → (req: filter x) )
-/

--def ofTrue (x: α) (req: filter x) : Filtered filter :=


end Filtered


end Nemonuri

end
