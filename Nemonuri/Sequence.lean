module

public import Mathlib.Data.ENat.Basic
public import Cslib.Foundations.Data.OmegaSequence.Init

@[expose] public section

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







end Sequence

end Nemonuri

end
