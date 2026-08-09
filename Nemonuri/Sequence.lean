module

/-
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

inductive EmptyLabel where
  | empty
  | nonempty
  deriving DecidableEq, Repr, Fintype

namespace EmptyLabel


@[defeq]
theorem ofNat_zero : EmptyLabel.ofNat 0 = .empty := rfl

@[defeq]
theorem ofNat_succ {n} : EmptyLabel.ofNat (.succ n) = .nonempty := rfl

theorem ofNat_empty_iff_eq_zero {n} : (EmptyLabel.ofNat n = .empty) ↔ (n = 0) := by
  cases n
  · simp [ofNat_zero]
  · simp [ofNat_succ]


def ofENat (en: ENat) : EmptyLabel := ENat.recTopCoe (EmptyLabel.nonempty) (fun n => EmptyLabel.ofNat n) en

@[defeq]
theorem ofENat_natCast {n} : ofENat (Nat.cast n) = ofNat n := rfl

@[defeq]
theorem ofENat_zero : ofENat 0 = .empty := rfl

@[defeq]
theorem ofENat_succ {n} : ofENat (Nat.succ n) = .nonempty := rfl

@[defeq]
theorem ofENat_top : ofENat ⊤ = .nonempty := rfl


scoped instance : HasLabel EmptyLabel Nat := ⟨ofNat⟩

scoped instance : HasLabel EmptyLabel ENat := ⟨ofENat⟩

attribute [scoped simp] ofNat_zero ofNat_succ ofENat_natCast ofENat_zero ofENat_succ ofENat_top


section List

variable {α: Type _} {a: α} {as: List α}

def ofList (as: List α) : EmptyLabel := match as with | .nil => .empty | .cons _ _ => .nonempty

@[defeq]
theorem ofList_nil : (ofList ([]: List α)) = .empty := rfl

@[defeq]
theorem ofList_cons : (ofList (a::as)) = .nonempty := rfl

scoped instance : HasLabel EmptyLabel (List α) := ⟨ofList⟩

attribute [scoped simp] ofList_nil ofList_cons

theorem ofList_eq_empty_iff_eq_nil : ((ofList as) = .empty) ↔ (as = []) := by
  cases as <;> simp

theorem ofList_eq_empty_iff_length_eq_zero : ((ofList as) = .empty) ↔ (as.length = 0) :=
  calc
    _ ↔ _ := ofList_eq_empty_iff_eq_nil
    _ ↔ _ := List.eq_nil_iff_length_eq_zero

theorem ofList_eq_nonempty_iff_ne_nil : ((ofList as) = .nonempty) ↔ (as ≠ []) := by
  cases as <;> simp

theorem ofList_eq_nonempty_iff_length_pos : ((ofList as) = .nonempty) ↔ (0 < as.length) :=
  calc
    _ ↔ _ := ofList_eq_nonempty_iff_ne_nil
    _ ↔ _ := List.ne_nil_iff_length_pos

theorem ofList_eq_ofNat : (ofList as) = (ofNat as.length) := by
  cases as <;> simp

end List

end EmptyLabel

open Cslib

inductive Sequence (α: Type _) where
  | finite (xs: List α)
  | infinite (xs: ωSequence α)

namespace Sequence

variable {α: Type _} {seq: Sequence α}


inductive Label where
  | finite
  | infinite
  deriving DecidableEq, Repr, Fintype

def toLabel : Sequence α → Label
  | .finite _ => .finite
  | .infinite _ => .infinite

instance : HasLabel Label (Sequence α) := ⟨toLabel⟩

/-
def isFinite : Sequence α → Bool
  | .finite _ => .true
  | .infinite _ => .false
-/

@[defeq, simp]
theorem finite_toLabel {xs: List α} : toLabel (.finite xs) = .finite := rfl

@[defeq, simp]
theorem infinite_toLabel {xs: ωSequence α} : toLabel (.infinite xs) = .infinite := rfl



def toList! : Sequence α → List α
  | .finite xs => xs
  | .infinite _ => []

def toList (seq: Sequence α) (req: seq.toLabel = .finite) : List α :=
  match seq with
  | .finite xs => xs
  | .infinite xs => absurd req (by simp)

theorem toList!_eq_toList (req: seq.toLabel = .finite)
  : seq.toList! = seq.toList req := by
  cases seq <;> try simp at req
  dsimp [toList!, toList]


@[defeq, simp]
theorem finite_toList (xs: List α) : toList (.finite xs) finite_toLabel = xs := rfl


def toωSequence (seq: Sequence α) (req: seq.toLabel = .infinite) : ωSequence α :=
  match seq with
  | .finite _ => absurd req (by simp)
  | .infinite xs => xs

@[defeq, simp]
theorem infinite_toωSequence (xs: ωSequence α) : toωSequence (.infinite xs) infinite_toLabel = xs := rfl


def length! (seq: Sequence α) : Nat := seq.toList!.length

def length (seq: Sequence α) (req: seq.toLabel = .finite) : Nat := seq.toList req |>.length

theorem length!_eq_length (req: seq.toLabel = .finite)
  : seq.length! = seq.length req := by
  dsimp [length!, length]
  rw [seq.toList!_eq_toList req]

def length? : Sequence α → ENat  --if h: seq.toLabel = .finite then seq.length h else ⊤
  | .finite xs => xs.length
  | .infinite _ => ⊤

def toEmptyLabel (seq: Sequence α) : EmptyLabel := seq.length? |> EmptyLabel.ofENat

instance : HasLabel EmptyLabel (Sequence α) := ⟨toEmptyLabel⟩

@[defeq, simp]
theorem finite_toEmptyLabel {xs} : toEmptyLabel (@finite α xs) = EmptyLabel.ofNat xs.length := by
  dsimp [toEmptyLabel, length?, EmptyLabel.ofENat]

@[defeq, simp]
theorem infinite_toEmptyLabel {xs} : toEmptyLabel (@infinite α xs) = .nonempty := by
  dsimp [toEmptyLabel, length?]
  dsimp [EmptyLabel.ofENat_top]

@[simp]
theorem false_of_empty_infinite (req1: seq.toEmptyLabel = .empty) (req2: seq.toLabel = .infinite) : False := by
  cases seq
  · simp at req2
  · simp at req1


@[simp]
theorem length?_eq_length_natCast (req: seq.toLabel = .finite)
  : seq.length? = Nat.cast (seq.length req) := by
  cases seq <;> try simp at req
  rfl

@[defeq, simp]
theorem finite_length_eq_toList_length (req: seq.toLabel = .finite)
  : seq.length req = (seq.toList req).length :=
  rfl

@[simp]
theorem length?_eq_top (req: seq.toLabel = .infinite)
  : seq.length? = ⊤ := by
  cases seq <;> try simp at req
  rfl

section ToEmptyLabel

open scoped EmptyLabel

theorem toEmptyLabel_eq_nonempty_iff_length?_pos
  : (seq.toEmptyLabel = .nonempty) ↔ (0 < seq.length?) := by
  rcases seq with xs | _
  · simp
    cases xs.length <;> simp
  · simp

theorem toEmptyLabel_eq_empty_iff_length?_eq_zero
  : (seq.toEmptyLabel = .empty) ↔ (seq.length? = 0) := by
  rcases seq with xs | _
  · simp
    rcases lm1: xs.length with _ | n
    · simp; exact List.eq_nil_of_length_eq_zero lm1
    · simp; exact List.ne_nil_of_length_eq_add_one lm1
  · simp

theorem toLabel_eq_finite_of_toEmptyLabel_eq_empty (req: seq.toEmptyLabel = .empty)
  : (seq.toLabel = .finite) := by
  rewrite [toEmptyLabel_eq_empty_iff_length?_eq_zero] at req
  cases seq <;> try simp at req
  dsimp

theorem toList_eq_nil_of_toEmptyLabel_eq_empty (req: seq.toEmptyLabel = .empty)
  : seq.toList (seq.toLabel_eq_finite_of_toEmptyLabel_eq_empty req) = [] := by
  have lm1 := seq.length?_eq_length_natCast (seq.toLabel_eq_finite_of_toEmptyLabel_eq_empty req)
  revert req; simp [toEmptyLabel_eq_empty_iff_length?_eq_zero]; intro req lm1
  rewrite [lm1] at req
  simpa using req

theorem toList_ne_nil_of_toEmptyLabel_eq_nonempty (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toLabel = .finite)
  : seq.toList req2 ≠ [] := by
  have lm1 := seq.length?_eq_length_natCast req2
  revert req1; simp [toEmptyLabel_eq_nonempty_iff_length?_pos]; intro req
  rewrite [lm1] at req
  simp at req
  exact List.ne_nil_of_length_pos req



end ToEmptyLabel






theorem lt_length?_iff_lt_toList_length (req: seq.toLabel = .finite) {i: Nat}
  : (i < seq.length?) ↔ (i < (seq.toList req).length) := by
  simp [req]

theorem lt_length? (req: seq.toLabel = .infinite) (i: Nat)
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
  (req1: seq.toLabel = .finite) (i: Nat) (req2: i < seq.length?)
  : seq[i]'(req2) = (seq.toList req1)[i]'((seq.lt_length?_iff_lt_toList_length req1).mp req2) := by
  cases seq <;> simp at req1
  · simp at req2 ⊢; rfl

@[simp]
theorem getElem_eq_app
  (req: seq.toLabel = .infinite) (i: Nat)
  : seq[i]'(lt_length? req i) = (seq.toωSequence req) i := by
  cases seq <;> simp at req
  · simp; rfl


def head (seq: Sequence α) (req: seq.toEmptyLabel = .nonempty) : α :=
  match lm1: seq with
  | .finite xs => xs.head (by
      suffices goal: (seq.toList ?h1) ≠ [] from by
        subst lm1; simpa using goal
      case h1 => subst lm1; dsimp
      refine seq.toList_ne_nil_of_toEmptyLabel_eq_nonempty ?_ _
      subst lm1; exact req )
  | .infinite xs => xs.head

def tail (seq: Sequence α) : Sequence α :=
  match seq with
  | .finite xs => xs.tail |> .finite
  | .infinite xs => xs.tail |> .infinite


def nil : Sequence α := .finite []

@[defeq, simp]
theorem nil_toLabel : (nil : Sequence α).toLabel = .finite := rfl

@[defeq, simp]
theorem nil_toEmptyLabel : (nil : Sequence α).toEmptyLabel = .empty := rfl

@[defeq, simp]
theorem nil_length?_eq_zero : (nil : Sequence α).length? = 0 := rfl

@[defeq, simp]
theorem nil_tail_eq_nil : (nil : Sequence α).tail = nil := rfl

theorem nil_eta (req: seq.toEmptyLabel = .empty) : nil = seq := by
  have lm1 := seq.toList_eq_nil_of_toEmptyLabel_eq_empty req
  cases seq <;> try simp at req
  simp at lm1
  subst lm1
  rfl


section Tail

@[simp]
theorem tail_toLabel : seq.tail.toLabel = seq.toLabel := by
  cases seq <;> rfl

theorem tail_preserves_toLabel : HasLabel.Preserves Label (@Sequence.tail α) := by
  refine .mk _ ?_
  intro x; symm; exact x.tail_toLabel

@[defeq]
theorem tail_finite {as} : (@finite α as).tail = (@finite α as.tail) := rfl

@[defeq]
theorem tail_infinite {as} : (@infinite α as).tail = (@infinite α as.tail) := rfl

theorem tail_toList (req: seq.toLabel = .finite)
  : seq.tail.toList (seq.tail_toLabel.trans req) = (seq.toList req).tail := by
  cases seq <;> try simp at req
  dsimp [tail_finite]

theorem tail_toωSequence (req: seq.toLabel = .infinite)
  : seq.tail.toωSequence (seq.tail_toLabel.trans req) = (seq.toωSequence req).tail := by
  cases seq <;> try simp at req
  dsimp [tail_infinite]

end Tail


def cons (head: α) (tail: Sequence α) : Sequence α :=
  match tail with
  | .finite xs => xs.cons head |> .finite
  | .infinite xs => xs.cons head |> .infinite

section Cons

variable {a: α} {as: Sequence α}

open scoped EmptyLabel
open scoped ωSequence

@[simp]
theorem cons_toLabel : (cons a as).toLabel = as.toLabel := by
  cases as <;> dsimp [cons]

theorem cons_preserves_toLabel : HasLabel.Preserves Label (Sequence.cons a) := by
  refine .mk _ ?_
  intro x; symm; exact cons_toLabel

@[simp]
theorem cons_toEmptyLabel : (cons a as).toEmptyLabel = .nonempty := by
  cases as <;> dsimp [cons]

@[simp]
theorem cons_head : (cons a as).head as.cons_toEmptyLabel = a := by
  cases as <;> rfl

@[simp]
theorem cons_tail : (cons a as).tail = as := by
  cases as <;> rfl


@[defeq]
theorem cons_finite {as} : (cons a (.finite as)) = (.finite (a :: as)) := rfl

@[defeq]
theorem cons_infinite {as} : (cons a (.infinite as)) = (.infinite (a ::ω as)) := rfl

theorem cons_toList (req: as.toLabel = .finite)
  : (cons a as).toList (cons_toLabel.trans req) = a :: (as.toList req) := by
  cases as <;> try simp at req
  dsimp [cons_finite]

theorem cons_toωSequence (req: as.toLabel = .infinite)
  : (cons a as).toωSequence (cons_toLabel.trans req) = a ::ω (as.toωSequence req) := by
  cases as <;> try simp at req
  · dsimp [cons_infinite]

theorem cons_eta (req: seq.toEmptyLabel = .nonempty)
  : (cons (seq.head req) seq.tail) = seq := by
  cases seq
  · dsimp [Sequence.head, Sequence.tail, Sequence.cons]
    congr
    simp
  · dsimp [Sequence.head, Sequence.tail, Sequence.cons]
    congr
    simp

end Cons

/-
theorem length?_ne_zero_iff_pos
  : (seq.length? ≠ 0) ↔ (0 < seq.length?) := by
  simp
-/

@[elab_as_elim]
def indNilCons
  {motive: Sequence α → Sort _}
  (nil: motive Sequence.nil)
  (cons: (head: α) → (tail: Sequence α) → motive (Sequence.cons head tail))
  (t: Sequence α)
  : motive t :=
  match lm1: t.toEmptyLabel with
  | .empty => nil |> Eq.subst (nil_eta lm1)
  | .nonempty => cons (t.head lm1) t.tail |> Eq.subst (cons_eta lm1)


section

variable {motive nil cons t}

@[defeq, simp]
theorem indNilCons_nil (req: t.toEmptyLabel = .empty)
  : (@indNilCons α motive nil cons t) = (nil |> Eq.subst (nil_eta req)) :=
  rfl

@[defeq, simp]
theorem indNilCons_cons (req: t.toEmptyLabel = .nonempty)
  : (@indNilCons α motive nil cons t) = (cons (t.head req) t.tail |> Eq.subst (cons_eta req)) :=
  rfl

end



def getLast (req1: seq.toEmptyLabel = .nonempty) (req2: seq.toLabel = .finite) : α :=
  (seq.toList req2).getLast (seq.toList_ne_nil_of_toEmptyLabel_eq_nonempty req1 req2)


inductive IsPrefix (as1: List α) : Sequence α → Prop where
  | finite (as2: List α) (req: as1.IsPrefix as2) : IsPrefix as1 (.finite as2)
  | infinite (as2: ωSequence α) (req: (as2.take as1.length) = as1) : IsPrefix as1 (.infinite as2)

namespace IsPrefix

theorem refl (as: List α) : IsPrefix as (.finite as) := by
  refine IsPrefix.finite _ ?_
  exact List.prefix_rfl

theorem lt_length?_of_lt_length {as1 as2} (h: @IsPrefix α as1 as2) {i: Nat} (req: i < as1.length)
  : (Nat.cast i) < as2.length? := by
  rcases h with ⟨as2, lm1⟩ | _
  · simp
    obtain ⟨as3, lm2⟩ := List.prefix_iff_exists_eq_append.mp lm1
    subst lm2
    simp only [List.length_append]
    calc
      i < _ := req
      _ ≤ _ := Nat.le_add_right _ _
  · simp

theorem getElem_eq {as1 as2} (h: @IsPrefix α as1 as2) {i: Nat} (req: i < as1.length)
  : as1[i]'(req) = as2[i]'(h.lt_length?_of_lt_length req) := by
  rcases h with ⟨as2, lm1⟩ | ⟨as2, lm1⟩
  · refine List.IsPrefix.getElem lm1 ?_
  · simp
    revert req
    rw [← lm1]
    exact ωSequence.take_get _ _ _

end IsPrefix

inductive IsSuffix (as1: List α) : Sequence α → Prop where
  | finite (as2: List α) (req: as1.IsSuffix as2) : IsSuffix as1 (.finite as2)

namespace IsSuffix

@[simp]
theorem not_infinite {as1 as2} : ¬(@IsSuffix α as1 (.infinite as2)) := nofun

theorem toLabel_eq_finite {as1 as2} (h: @IsSuffix α as1 as2) : as2.toLabel = .finite := by
  cases as2
  · simp
  · simp at h

theorem refl (as: List α) : IsSuffix as (.finite as) := by
  refine IsSuffix.finite _ ?_
  exact List.suffix_rfl

theorem lt_length?_of_lt_length {as1 as2} (h: @IsSuffix α as1 as2) {i: Nat} (req: i < as1.length)
  : (Nat.cast i) < as2.length? := by
  rcases h with ⟨as2, lm1⟩
  simp
  obtain ⟨as3, lm2⟩ := List.suffix_iff_exists_eq_append.mp lm1
  subst lm2
  simp only [List.length_append]
  calc
    i < _ := req
    _ ≤ _ := Nat.le_add_left _ _

theorem getElem_req_of_lt_length {as1 as2} (h: @IsSuffix α as1 as2) {i: Nat} (req: i < as1.length)
  : ((as2.length h.toLabel_eq_finite) - as1.length + i) < as2.length? := by
  have lm2 := h.lt_length?_of_lt_length req
  rcases h with ⟨as2, lm1⟩
  simp at lm2 ⊢
  rw [← ENat.coe_sub]
  rw [← ENat.coe_add]
  refine ENat.coe_lt_coe.mpr ?_
  have lm3 := List.IsSuffix.length_le lm1
  omega


theorem getElem_eq {as1 as2} (h: @IsSuffix α as1 as2) {i: Nat} (req: i < as1.length)
  : as1[i]'(req) = as2[(as2.length h.toLabel_eq_finite) - as1.length + i]'(h.getElem_req_of_lt_length req) := by
  rcases h with ⟨as2, lm1⟩
  simp
  refine List.IsSuffix.getElem lm1 ?_



end IsSuffix




def ofListRepeat (l: List α) (req: l ≠ []) : Sequence α := .infinite (ωSequence.ofListRepeat l req)



/-
namespace Label


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
-/


end Sequence

end Nemonuri



end
-/
