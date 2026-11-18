module


public import Mathlib.Logic.Equiv.Defs
public import Nemonuri.TypeLists.IterDecidableEq

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists

/-
protected def List.append : (xs ys : List α) → List α
  | nil,       bs => bs
  | cons a as, bs => cons a (List.append as bs)
-/


abbrev typeAppend.{u} : List (Type u) → List (Type u) → List (Type u)
  | [], tys2 => tys2
  | ty::tys1, tys2 => ty::(typeAppend tys1 tys2)


infixl:65 " ++ᵗ " => typeAppend


inductive IterSum.{u} : List (Type u) → Type _ where
  | ofVal (Head: Type u) (tail: List (Type u)) (head: Head) : IterSum (Head :: tail)
  | cons (Head: Type u) (tail: List (Type u)) (isum: IterSum tail) : IterSum (Head :: tail)

namespace IterSum

universe u


theorem not_nil : (IterSum []) → False := by
  intro isum
  rcases isum


protected def elimNil {C: Sort*} (isum: IterSum []) : C := isum.not_nil.elim


theorem nil_prop_eq_true (p: (tys: List (Type u)) → (IterSum tys) → Prop) (isum: IterSum []) : p [] isum = True := by
  exact isum.elimNil

abbrev types {tys: List (Type u)} (_: IterSum tys) : List (Type u) := tys

@[defeq]
theorem types_def {tys: List (Type u)} {isum: IterSum tys} : isum.types = tys := rfl

def valIndexAt (tys: List (Type u)) (isum: IterSum tys) : Nat :=
  match tys with
  | [] => isum.elimNil
  | _::tys =>
  match isum with
  | ofVal _ _ _ => 0
  | cons _ _ isum =>
    1 + isum.valIndexAt tys

def valIndex {tys: List (Type u)} (isum: IterSum tys) : Nat := isum.valIndexAt tys

@[defeq]
theorem valIndex_def {tys: List (Type u)} {isum: IterSum tys} : isum.valIndex = isum.valIndexAt tys := rfl

theorem valIndex_lt_types_length {tys: List (Type u)} (isum: IterSum tys) : isum.valIndex < isum.types.length := by
  dsimp [types]
  rcases tys with _ | ⟨ty, tys⟩
  · exact isum.elimNil
  · dsimp [valIndex]
    rcases isum with ⟨_,_,head⟩ | ⟨_,_,isum⟩
    · simp only [valIndexAt]
      exact Nat.zero_lt_succ _
    · simp only [valIndexAt]
      conv => lhs; rw [Nat.add_comm]
      refine Nat.add_lt_add_right ?_ 1
      dsimp [← valIndex_def]
      exact isum.valIndex_lt_types_length

def valIndexFin {tys: List (Type u)} (isum: IterSum tys) : Fin (tys.length) := ⟨isum.valIndex, isum.valIndex_lt_types_length⟩


theorem ofVal_valIndex_eq_zero {tys: List (Type u)} {Ty: Type u} {v: Ty} : (ofVal Ty tys v).valIndex = 0 := by
  dsimp [valIndex_def]
  simp [valIndexAt]

theorem ofVal_valIndexFin_eq_zero {tys: List (Type u)} {Ty: Type u} {v: Ty} : (ofVal Ty tys v).valIndexFin = 0 := by
  dsimp [valIndexFin]
  simp [ofVal_valIndex_eq_zero]


abbrev ValTypeAt (tys: List (Type u)) (isum: IterSum tys) : Type u :=
  match tys with
  | [] => isum.elimNil
  | ty::tys =>
  match isum with
  | ofVal _ _ _ => ty
  | cons _ _ isum => isum.ValTypeAt tys

abbrev ValType {tys: List (Type u)} (isum: IterSum tys) : Type u := isum.ValTypeAt tys


theorem valType_eq_types_getElem {tys: List (Type u)} (isum: IterSum tys) : isum.ValType = isum.types[isum.valIndex]'(isum.valIndex_lt_types_length) := by
  dsimp [types]
  rcases tys with _ | ⟨ty, tys⟩
  · exact isum.elimNil
  · dsimp [ValType, valIndex]
    rcases isum with ⟨_,_,_⟩ | ⟨_,_,isum⟩
    · simp [valIndexAt]
      unfold ValTypeAt
      simp only
    · simp [valIndexAt]
      unfold ValTypeAt
      simp only
      conv => rhs; arg 2; rw [Nat.add_comm]
      simp
      exact isum.valType_eq_types_getElem


theorem valType_eq_types_getElem_valIndexFin {tys: List (Type u)} (isum: IterSum tys) : isum.ValType = isum.types[isum.valIndexFin] := isum.valType_eq_types_getElem



def val {tys: List (Type u)} (isum: IterSum tys) : isum.ValType :=
  match tys, isum with
  | _, .ofVal _ _ head => head
  | _, .cons _ _ isum => isum.val
/-
  match tys with
  | [] => isum.elimNil
  | _::tys =>
  match isum with
  | ofVal _ _ head => head
  | cons _ _ isum => isum.valAt tys
-/

--def val {tys: List (Type u)} (isum: IterSum tys) : isum.ValType := isum.valAt tys


@[defeq, simp]
theorem ofVal_val {Ty: Type u} {tys: List (Type u)} {v: Ty} : (ofVal Ty tys v).val = v := by
  dsimp [val]

@[defeq, simp]
theorem cons_val {Ty: Type u} {tys: List (Type u)} {isum: IterSum tys} : (cons Ty tys isum).val = isum.val := by
  dsimp [val]




def valAsGetElem {tys: List (Type u)} (isum: IterSum tys) : isum.types[isum.valIndexFin] := isum.valType_eq_types_getElem_valIndexFin.mp isum.val



theorem valType_eq_of_valIndex_eq (tys: List (Type u)) (isum1 isum2: IterSum tys) (req: isum1.valIndex = isum2.valIndex) : isum1.ValType = isum2.ValType := by
  rw [isum1.valType_eq_types_getElem, isum2.valType_eq_types_getElem]
  dsimp [types]
  simp only [req]


theorem valType_of_single {Ty: Type u} (isum: IterSum [Ty]) : isum.ValType = Ty := by
  dsimp [ValType]
  rcases isum with ⟨_,_,head⟩ | ⟨_,_,isum⟩
  · unfold ValTypeAt
    simp only
  · exact isum.elimNil


def singleToVal {Ty: Type u} (isum: IterSum [Ty]) : Ty :=
  match isum with
  | .ofVal _ _ v => v
  | .cons _ _ isum => isum.elimNil

def singleOfVal {Ty: Type u} (v: Ty) : IterSum [Ty] := .ofVal Ty [] v

theorem singleOfVal_singleToVal_leftInverse (Ty: Type u) : Function.LeftInverse (@singleOfVal Ty) (singleToVal) := by
  intro isum
  rcases isum with ⟨_,_,_⟩ | ⟨_,_,isum⟩
  · dsimp [singleOfVal, singleToVal]
    simp only
  · exact isum.elimNil

theorem singleOfVal_singleToVal_rightInverse (Ty: Type u) : Function.RightInverse (@singleOfVal Ty) (singleToVal) := by
  intro v
  dsimp [singleToVal, singleOfVal]
  simp only


def equivOfSingle (Ty: Type u) : IterSum [Ty] ≃ Ty where
  toFun := singleToVal
  invFun := singleOfVal
  left_inv := singleOfVal_singleToVal_leftInverse Ty
  right_inv := singleOfVal_singleToVal_rightInverse Ty


def doubleToSum {Ty1 Ty2: Type u} (isum: IterSum [Ty1, Ty2]) : Ty1 ⊕ Ty2 :=
  match isum with
  | .ofVal _ _ v => .inl v
  | .cons _ _ isum =>
  match isum with
  | .ofVal _ _ v => .inr v
  | .cons _ _ isum => isum.elimNil

def doubleOfSum {Ty1 Ty2: Type u} (sum: Ty1 ⊕ Ty2) : IterSum [Ty1, Ty2] :=
  match sum with
  | .inl v => .ofVal Ty1 [Ty2] v
  | .inr v => (.ofVal Ty2 [] v) |> .cons Ty1 _


theorem doubleOfSum_doubleToSum_leftInverse (Ty1 Ty2: Type u) : Function.LeftInverse (@doubleOfSum Ty1 Ty2) (doubleToSum) := by
  intro isum
  rcases isum with _ | ⟨_,_,isum⟩
  · simp only [doubleToSum]
    dsimp [doubleOfSum]
  · rcases isum with _ | ⟨_,_,isum⟩
    · simp only [doubleToSum]
      dsimp [doubleOfSum]
    · exact isum.elimNil


theorem doubleOfSum_doubleToSum_rightInverse (Ty1 Ty2: Type u) : Function.RightInverse (@doubleOfSum Ty1 Ty2) (doubleToSum) := by
  intro sum
  rcases sum with ⟨v⟩ | ⟨v⟩ <;> (simp only [doubleOfSum, doubleToSum])


def equivOfDouble (Ty1 Ty2: Type u) : IterSum [Ty1, Ty2] ≃ (Ty1 ⊕ Ty2) where
  toFun := doubleToSum
  invFun := doubleOfSum
  left_inv := doubleOfSum_doubleToSum_leftInverse _ _
  right_inv := doubleOfSum_doubleToSum_rightInverse _ _

@[ext]
protected theorem ext (tys: List (Type u)) (isum1 isum2: IterSum tys) (req1: isum1.valIndex = isum2.valIndex) (req2: isum1.val ≍ isum2.val) : isum1 = isum2 := by
  rcases tys with _ | ⟨Ty, tys⟩
  · exact isum1.elimNil
  · rcases isum1 with _ | ⟨_,_,isum1⟩
    <;> rcases isum2 with _ | ⟨_,_,isum2⟩
    · dsimp [val] at req2
      simp at req2 ⊢
      exact eq_of_heq req2
    · dsimp [valIndex] at req1
      unfold valIndexAt at req1
      simp at req1
      conv at req1 => rhs; rw [Nat.add_comm]
      exact Nat.zero_ne_add_one _ req1 |>.elim
    · dsimp [valIndex] at req1
      unfold valIndexAt at req1
      simp only at req1
      conv at req1 => rw [Eq.comm]; rhs; rw [Nat.add_comm]
      exact Nat.zero_ne_add_one _ req1 |>.elim
    · simp
      simp [valIndex, valIndexAt] at req1
      dsimp at req2
      exact IterSum.ext tys isum1 isum2 req1 req2

theorem ne_of_valIndex_ne (tys: List (Type u)) (isum1 isum2: IterSum tys) (req: isum1.valIndex ≠ isum2.valIndex) : isum1 ≠ isum2 := by
  intro lm1
  rewrite [lm1] at req
  exact req (Eq.refl _)

theorem valType_eq_head_of_valIndex_eq_zero {Ty: Type u} {tys: List (Type u)} (isum: IterSum (Ty::tys)) (req: isum.valIndex = 0) : isum.ValType = Ty := by
  rcases isum with _ | ⟨_,_,_⟩
  · simp [ValType]
    unfold ValTypeAt
    simp only
  · simp [valIndex] at req
    unfold valIndexAt at req
    simp at req



def getFin? {tys: List (Type u)} (isum: IterSum tys) (i: Fin tys.length) : Option isum.types[i] :=
  let ⟨i, lm1⟩ := i
  if h1: isum.valIndex = i then
    .some (h1 ▸ (isum.valType_eq_types_getElem ▸ isum.val))
  else
    .none

theorem getFin?_isSome_of_valIndex_eq {tys: List (Type u)} (isum: IterSum tys) (i: Fin tys.length) (req: isum.valIndex = ↑i)
  : (isum.getFin? i).isSome = .true := by
  dsimp [getFin?]
  simp [req]

def getFin {tys: List (Type u)} (isum: IterSum tys) (i: Fin tys.length) (req: isum.valIndex = ↑i) : isum.types[i] :=
  (isum.getFin? i).get (isum.getFin?_isSome_of_valIndex_eq i req)


def areEq (tys: List (Type u)) (isum1 isum2: IterSum tys) (iter: IterDecidableEq tys) : Bool :=
  match tys with
  | [] => isum1.elimNil
  | _::tys =>
  match isum1, isum2, iter with
  | .ofVal _ _ v1, .ofVal _ _ v2, .cons _ _ _ _ => decide (v1 = v2)
  | .cons _ _ isum1, .cons _ _ isum2, .cons _ _ _ iter => areEq tys isum1 isum2 iter
  | .ofVal .., .cons .., _
  | .cons .., .ofVal .., _ => .false

theorem areEq_eq_true_iff_eq {tys: List (Type u)} {isum1 isum2: IterSum tys} {iter: IterDecidableEq tys}
  : (areEq tys isum1 isum2 iter = .true) ↔ (isum1 = isum2) := by
  rcases tys with _ | ⟨Ty, tys⟩
  · exact isum1.elimNil
  · rcases isum1 with _ | ⟨_,_,isum1⟩
    <;> rcases isum2 with _ | ⟨_,_,isum2⟩
    <;> rcases iter with _ | ⟨_,_,_,iter⟩
    <;> (
      simp only [areEq]
      simp )
    exact areEq_eq_true_iff_eq

protected instance decidableEq (tys: List (Type u)) [HasIterDecidableEq tys] : DecidableEq (IterSum tys) :=
  fun isum1 isum2 => decidable_of_iff (areEq tys isum1 isum2 (@HasIterDecidableEq.iterDecidableEq tys _) = .true) areEq_eq_true_iff_eq

@[implicit_reducible]
def append (tys1: List (Type u)) {tys2: List (Type u)} (isum: IterSum tys2) : IterSum (tys1 ++ tys2) :=
  match tys1 with
  | [] => isum
  | Ty::tys1 => .cons Ty _ (append tys1 isum)

@[elab_as_elim]
def recSingle.{um}
  {motive: (Ty: Type u) → (IterSum [Ty]) → Sort um}
  (ofVal: (Ty: Type u) → (v: Ty) → motive Ty (.ofVal Ty [] v))
  (Ty: Type u) (isum: IterSum [Ty])
  : motive Ty isum :=
  match isum with
  | .ofVal _ _ v => ofVal Ty v

@[elab_as_elim]
def recSingleOn.{um}
  {motive: (Ty: Type u) → (IterSum [Ty]) → Sort um}
  {Ty: Type u} (isum: IterSum [Ty])
  (ofVal: (Ty: Type u) → (v: Ty) → motive Ty (.ofVal Ty [] v))
  : motive Ty isum :=
  recSingle ofVal Ty isum

end IterSum


end Nemonuri.TypeLists

end
