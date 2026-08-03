module

public import Mathlib.Data.ENat.Basic
public import Cslib.Foundations.Data.OmegaSequence.Init
public import Nemonuri.HasLabel
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

protected def List.repeat {α: Type _} (as: List α) (req: as ≠ []) (i: Nat) : α :=
  let i0 : Nat := i % as.length
  as[i0]'(by subst i0; refine Nat.mod_lt i ?_; exact List.length_pos_of_ne_nil req)

protected def Cslib.ωSequence.ofListRepeat {α: Type _} (as: List α) (req: as ≠ []) : Cslib.ωSequence α := ⟨as.repeat req⟩


namespace Nemonuri

open Cslib

inductive Sequence (α: Type _) where
  | finite (xs: List α)
  | infinite (xs: ωSequence α)

namespace Sequence

variable {α: Type _} {seq: Sequence α}


def isFinite : Sequence α → Bool
  | .finite _ => .true
  | .infinite _ => .false

@[simp, grind =]
theorem isFinite_finite {xs: List α} : isFinite (.finite xs) = .true := rfl

@[simp, grind =]
theorem isFinite_infinite {xs: ωSequence α} : isFinite (.infinite xs) = .false := rfl

theorem isFinite_iff_eq_finite
  : (seq.isFinite = .true) ↔ ∃xs, seq = (.finite xs) := by
  cases seq <;> simp


def isInfinite : Sequence α → Bool
  | .finite _ => .false
  | .infinite _ => .true

@[simp, grind =]
theorem isInfinite_finite {xs: List α} : isInfinite (.finite xs) = .false := rfl

@[simp, grind =]
theorem isInfinite_infinite {xs: ωSequence α} : isInfinite (.infinite xs) = .true := rfl

theorem isInfinite_iff_eq_infinite
  : seq.isInfinite ↔ ∃xs, seq = (.infinite xs) := by
  cases seq <;> simp


@[simp, grind =]
theorem not_isFinite_eq_isInfinite
  : (!seq.isFinite) = seq.isInfinite := by
  cases seq <;> simp

@[simp, grind =]
theorem not_isInfinite_eq_isFinite
  : (!seq.isInfinite) = seq.isFinite := by
  cases seq <;> simp

@[simp]
theorem isFinite_eq_false_iff
  : seq.isFinite = .false ↔ seq.isInfinite = .true := by
  cases seq <;> simp

@[simp]
theorem isInfinite_eq_false_iff
  : seq.isInfinite = .false ↔ seq.isFinite = .true := by
  cases seq <;> simp


def toList! : Sequence α → List α
  | .finite xs => xs
  | .infinite _ => []

def toList (seq: Sequence α) (req: seq.isFinite) : List α :=
  match seq with
  | .finite xs => xs
  | .infinite xs => absurd req (by simp)

theorem toList!_eq_toList (req: seq.isFinite)
  : seq.toList! = seq.toList req := by
  rewrite [seq.isFinite_iff_eq_finite] at req
  obtain ⟨xs, lm1⟩ := req
  subst lm1
  dsimp [toList!, toList]

@[simp]
theorem toList_eq (xs: List α) : (Sequence.finite xs).toList isFinite_finite = xs := rfl


def toωSequence (seq: Sequence α) (req: seq.isInfinite) : ωSequence α :=
  match seq with
  | .finite _ => absurd req (by simp)
  | .infinite xs => xs

@[simp]
theorem toωSequence_eq (xs: ωSequence α) : (Sequence.infinite xs).toωSequence isInfinite_infinite = xs := rfl


def length! (seq: Sequence α) : Nat := seq.toList!.length

def length (seq: Sequence α) (req: seq.isFinite) : Nat := seq.toList req |>.length

theorem length!_eq_length (req: seq.isFinite)
  : seq.length! = seq.length req := by
  dsimp [length!, length]
  rw [seq.toList!_eq_toList req]

def length? (seq: Sequence α) : ENat := if h: seq.isFinite then seq.length h else ⊤

@[simp]
theorem length?_eq_length_natCast (req: seq.isFinite)
  : seq.length? = Nat.cast (seq.length req) := by
  dsimp [length?]
  simp [req]

@[simp]
theorem finite_length_eq_toList_length (req: seq.isFinite)
  : seq.length req = (seq.toList req).length :=
  rfl

theorem lt_length?_iff_lt_toList_length
  (req: seq.isFinite) (i: Nat)
  : (i < seq.length?) ↔ (i < (seq.toList req).length) := by
  simp [req]


@[simp]
theorem length?_eq_top (req: seq.isInfinite)
  : seq.length? = ⊤ := by
  rewrite [← seq.not_isFinite_eq_isInfinite, Bool.not_eq_true'] at req
  dsimp [length?]
  simp [req]

theorem lt_length? (req: seq.isInfinite) (i: Nat)
  : i < seq.length? := by
  simp [req]




def getAt (seq: Sequence α) (i: Nat) (req: i < seq.length?) : α :=
  match seq with
  | .finite xs => xs[i]'(by simpa using req)
  | .infinite xs => xs i


instance : GetElem (Sequence α) Nat α (fun seq i => i < seq.length?) where
  getElem seq i req := seq.getAt i req


@[simp]
theorem getElem_eq_list
  (req1: seq.isFinite) (i: Nat) (req2: i < seq.length?)
  : seq[i]'(req2) = (seq.toList req1)[i]'((seq.lt_length?_iff_lt_toList_length req1 i).mp req2) := by
  cases seq <;> simp at req1
  · simp at req2 ⊢; rfl

@[simp]
theorem getElem_eq_app
  (req: seq.isInfinite) (i: Nat)
  : seq[i]'(lt_length? req i) = (seq.toωSequence req) i := by
  cases seq <;> simp at req
  · simp; rfl


def head (seq: Sequence α) (req: 0 < seq.length?) : α :=
  match seq with
  | .finite xs => xs.head (by simpa [List.ne_nil_iff_length_pos] using req)
  | .infinite xs => xs.head

def tail (seq: Sequence α) : Sequence α :=
  match seq with
  | .finite xs => xs.tail |> .finite
  | .infinite xs => xs.tail |> .infinite


def nil : Sequence α := .finite []

@[defeq, simp]
theorem nil_length?_eq_zero : (nil : Sequence α).length? = 0 := rfl

@[defeq, simp]
theorem nil_tail_eq_nil : (nil : Sequence α).tail = nil := rfl

theorem nil_eta (req: seq.length? = 0) : nil = seq := by
  cases seq <;> simp at req
  · subst req; rfl

@[defeq, simp]
theorem nil_isFinite : (nil : Sequence α).isFinite = .true := rfl


def cons (head: α) (tail: Sequence α) : Sequence α :=
  match tail with
  | .finite xs => xs.cons head |> .finite
  | .infinite xs => xs.cons head |> .infinite

@[simp]
theorem cons_length?_pos {a as} : 0 < (@cons α a as).length? := by
  cases as <;> dsimp [cons] <;> simp

@[simp]
theorem cons_head {a as} : (@cons α a as).head cons_length?_pos = a := by
  cases as <;> rfl

@[simp]
theorem cons_tail {a as} : (@cons α a as).tail = as := by
  cases as <;> rfl

@[simp]
theorem cons_isFinite {a as} : (@cons α a as).isFinite = as.isFinite := by
  cases as <;> dsimp [cons]

@[defeq]
theorem cons_finite {a as} : (@cons α a (.finite as)) = (.finite (a :: as)) := rfl

@[simp]
theorem cons_isInfinite {a as} : (@cons α a as).isInfinite = as.isInfinite := by
  apply Bool.not_inj
  simp

open scoped ωSequence in
@[defeq]
theorem cons_infinite {a as} : (@cons α a (.infinite as)) = (.infinite (a ::ω as)) := rfl

theorem cons_eta (req: 0 < seq.length?)
  : cons (seq.head req) seq.tail = seq := by
  dsimp [head, tail]
  split <;> split <;> (rename_i lm1; simp at lm1) <;>
  (subst lm1; dsimp [cons]; congr; simp)

theorem length?_ne_zero_iff_pos
  : (seq.length? ≠ 0) ↔ (0 < seq.length?) := by
  simp

@[elab_as_elim]
def indNilCons
  {motive: Sequence α → Sort _}
  (nil: motive Sequence.nil)
  (cons: (head: α) → (tail: Sequence α) → motive (Sequence.cons head tail))
  (t: Sequence α)
  : motive t :=
  if lm1: t.length? = 0 then
    nil |> Eq.subst (nil_eta lm1)
  else
    have lm2 := length?_ne_zero_iff_pos.mp lm1
    cons (t.head lm2) t.tail |> Eq.subst (cons_eta lm2)

section

variable {motive nil cons t}

@[defeq, simp]
theorem indNilCons_nil (req: t.length? = 0)
  : (@indNilCons α motive nil cons t) = (nil |> Eq.subst (nil_eta req)) :=
  rfl

@[defeq, simp]
theorem indNilCons_cons (req: 0 < t.length?)
  : (@indNilCons α motive nil cons t) = (cons (t.head req) t.tail |> Eq.subst (cons_eta req)) :=
  rfl

end

theorem tail_isFinite : seq.tail.isFinite = seq.isFinite := by
  cases seq <;> dsimp [tail]

@[defeq]
theorem tail_finite {as} : (@finite α as).tail = (@finite α as.tail) := rfl

theorem tail_isInfinite : seq.tail.isInfinite = seq.isInfinite := by
  apply Bool.not_inj
  simp [tail_isFinite]

@[defeq]
theorem tail_infinite {as} : (@infinite α as).tail = (@infinite α as.tail) := rfl


def getLast (req1: 0 < seq.length?) (req2: seq.isFinite) : α := (seq.toList req2).getLast (by simp [req2] at req1; exact List.length_pos_iff.mp req1)


inductive IsPrefix (as1: List α) : Sequence α → Prop where
  | finite (as2: List α) (req: as1.IsPrefix as2) : IsPrefix as1 (.finite as2)
  | infinite (as2: ωSequence α) (req: (as2.take as1.length) = as1) : IsPrefix as1 (.infinite as2)

inductive IsSuffix (as1: List α) : Sequence α → Prop where
  | finite (as2: List α) (req: as1.IsSuffix as2) : IsSuffix as1 (.finite as2)


@[simp]
theorem infinite_not_isSuffix {as1 as2} : ¬(@IsSuffix α as1 (.infinite as2)) := nofun


def ofListRepeat (l: List α) (req: l ≠ []) : Sequence α := .infinite (ωSequence.ofListRepeat l req)

inductive Label where
  | finite
  | infinite
  deriving DecidableEq, Repr

def toLabel : Sequence α → Label
  | .finite _ => .finite
  | .infinite _ => .infinite


namespace Label

deriving instance Fintype for Label

instance : HasLabel Label (Sequence α) := ⟨toLabel⟩

attribute [local simp] HasLabel.Preserves

theorem tail_preserves_label : HasLabel.Preserves Label (@Sequence.tail α) := by
  dsimp; intro x; cases x <;> rfl

theorem cons_preserves_label {a} : HasLabel.Preserves Label (@Sequence.cons α a) := by
  dsimp; intro x; cases x <;> rfl

@[defeq, simp]
theorem finite_toLabel {as} : (@Sequence.finite α as).toLabel = .finite := rfl

@[defeq, simp]
theorem infinite_toLabel {as} : (@Sequence.infinite α as).toLabel = .infinite := rfl

end Label


end Sequence

end Nemonuri



end
