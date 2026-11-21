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



inductive IterSum.{u} : Type u → List (Type u) → Type _ where
  | ofVal (Head: Type u) (tail: List (Type u)) (v: Head) : IterSum Head tail
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (isum: IterSum Head2 tail) : IterSum Head1 (Head2::tail)

namespace IterSum

universe u

/-
theorem not_nil : (IterSum []) → False := by
  intro isum
  rcases isum


protected def elimNil {C: Sort*} (isum: IterSum []) : C := isum.not_nil.elim


theorem nil_prop_eq_true (p: (tys: List (Type u)) → (IterSum tys) → Prop) (isum: IterSum []) : p [] isum = True := by
  exact isum.elimNil
-/

def types {Ty: Type u} {tys: List (Type u)} (_: IterSum Ty tys) : List (Type u) := Ty::tys

@[defeq]
theorem types_def {Ty: Type u} {tys: List (Type u)} {isum: IterSum Ty tys} : isum.types = Ty::tys := rfl

theorem types_length_pos {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : 0 < isum.types.length := by simp [types_def]

instance {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : NeZero (isum.types.length) where
  out := Nat.pos_iff_ne_zero.mp isum.types_length_pos




def length {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : Nat := isum.types.length

@[defeq]
theorem length_def {Ty: Type u} {tys: List (Type u)} {isum: IterSum Ty tys} : isum.length = isum.types.length := rfl

@[defeq]
theorem length_eq_length_add_one {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.length = tys.length + 1 := by
  dsimp [length_def, types_def]




def valIndex {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : Nat :=
  match tys, isum with
  | _, .ofVal _ _ _ => 0
  | _, .cons _ _ _ isum => isum.valIndex + 1


@[defeq, simp]
theorem valIndex_ofVal {Ty: Type u} {tys: List (Type u)} (v: Ty) : (ofVal Ty tys v).valIndex = 0 := rfl

@[defeq, simp]
theorem valIndex_cons {Ty1 Ty2: Type u} {tys: List (Type u)} (isum: IterSum Ty2 tys) : (cons Ty1 Ty2 tys isum).valIndex = isum.valIndex + 1 := rfl


theorem valIndex_lt_length {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.valIndex < isum.length := by
  dsimp [length_eq_length_add_one]
  rcases isum with _ | ⟨_,_,_,isum⟩
  · dsimp
    exact Nat.zero_lt_succ _
  · dsimp
    refine Nat.add_lt_add_right ?_ 1
    exact isum.valIndex_lt_length


theorem valIndex_lt_types_length {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.valIndex < isum.types.length :=
  isum.length_def ▸ isum.valIndex_lt_length



def valIndexFin {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : Fin (isum.types.length) := ⟨isum.valIndex, isum.valIndex_lt_types_length⟩

@[defeq, simp]
theorem ofVal_valIndexFin_eq_zero {tys: List (Type u)} {Ty: Type u} {v: Ty} : (ofVal Ty tys v).valIndexFin = 0 := by
  dsimp [valIndexFin]
  rfl



def ValType {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : Type u :=
  match isum with
  | .ofVal _ _ _ => Ty
  | .cons _ _ _ isum => isum.ValType


@[defeq, simp]
theorem valType_ofVal {Ty: Type u} {tys: List (Type u)} (v: Ty) : (ofVal Ty tys v).ValType = Ty := rfl

@[defeq, simp]
theorem valType_cons {Ty1 Ty2: Type u} {tys: List (Type u)} (isum: IterSum Ty2 tys) : (cons Ty1 Ty2 tys isum).ValType = isum.ValType := rfl


theorem valType_eq_types_getElem {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.ValType = isum.types[isum.valIndex]'(isum.valIndex_lt_types_length) := by
  rcases isum with _ | ⟨_,_,_,isum⟩
  · dsimp [types_def]
  · dsimp [types_def]
    exact isum.valType_eq_types_getElem



theorem valType_eq_types_getElem_valIndexFin {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.ValType = isum.types[isum.valIndexFin] := isum.valType_eq_types_getElem



def val {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.ValType :=
  match isum with
  | .ofVal _ _ v => v
  | .cons _ _ _ isum => isum.val

@[defeq, simp]
theorem ofVal_val {Ty: Type u} {tys: List (Type u)} {v: Ty} : (ofVal Ty tys v).val = v := by
  dsimp [val]

@[defeq, simp]
theorem cons_val {Ty1 Ty2: Type u} {tys: List (Type u)} {isum: IterSum Ty2 tys} : (cons Ty1 Ty2 tys isum).val = isum.val := by
  dsimp [val]




def valAsGetElem {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : isum.types[isum.valIndexFin] := isum.valType_eq_types_getElem_valIndexFin.mp isum.val



theorem valType_eq_of_valIndex_eq {Ty: Type u} (tys: List (Type u)) (isum1 isum2: IterSum Ty tys) (req: isum1.valIndex = isum2.valIndex) : isum1.ValType = isum2.ValType := by
  rw [isum1.valType_eq_types_getElem, isum2.valType_eq_types_getElem]
  dsimp [types]
  simp only [req]
  rfl

@[simp]
theorem valType_of_single {Ty: Type u} (isum: IterSum Ty []) : isum.ValType = Ty := by
  rcases isum
  dsimp


def singleToVal {Ty: Type u} (isum: IterSum Ty []) : Ty :=
  match isum with
  | .ofVal _ _ v => v

def singleOfVal {Ty: Type u} (v: Ty) : IterSum Ty [] := .ofVal Ty [] v

theorem singleOfVal_singleToVal_leftInverse (Ty: Type u) : Function.LeftInverse (@singleOfVal Ty) (singleToVal) := by
  intro isum
  rcases isum with ⟨_,_,_⟩ | _
  · dsimp [singleOfVal, singleToVal]

theorem singleOfVal_singleToVal_rightInverse (Ty: Type u) : Function.RightInverse (@singleOfVal Ty) (singleToVal) := by
  intro v
  dsimp [singleToVal, singleOfVal]


def equivOfSingle (Ty: Type u) : IterSum Ty [] ≃ Ty where
  toFun := singleToVal
  invFun := singleOfVal
  left_inv := singleOfVal_singleToVal_leftInverse Ty
  right_inv := singleOfVal_singleToVal_rightInverse Ty


def doubleToSum {Ty1 Ty2: Type u} (isum: IterSum Ty1 [Ty2]) : Ty1 ⊕ Ty2 :=
  match isum with
  | .ofVal _ _ v => .inl v
  | .cons _ _  _ isum =>
  match isum with
  | .ofVal _ _ v => .inr v

def doubleOfSum {Ty1 Ty2: Type u} (sum: Ty1 ⊕ Ty2) : IterSum Ty1 [Ty2] :=
  match sum with
  | .inl v => .ofVal Ty1 [Ty2] v
  | .inr v => (.ofVal Ty2 [] v) |> .cons Ty1 _ _


theorem doubleOfSum_doubleToSum_leftInverse (Ty1 Ty2: Type u) : Function.LeftInverse (@doubleOfSum Ty1 Ty2) (doubleToSum) := by
  intro isum
  rcases isum with _ | ⟨_,_,_,isum⟩
  · simp only [doubleToSum]
    dsimp [doubleOfSum]
  · rcases isum with _ | ⟨_,_,_,isum⟩
    · simp only [doubleToSum]
      dsimp [doubleOfSum]


theorem doubleOfSum_doubleToSum_rightInverse (Ty1 Ty2: Type u) : Function.RightInverse (@doubleOfSum Ty1 Ty2) (doubleToSum) := by
  intro sum
  rcases sum with ⟨v⟩ | ⟨v⟩ <;> (simp only [doubleOfSum, doubleToSum])


def equivOfDouble (Ty1 Ty2: Type u) : IterSum Ty1 [Ty2] ≃ (Ty1 ⊕ Ty2) where
  toFun := doubleToSum
  invFun := doubleOfSum
  left_inv := doubleOfSum_doubleToSum_leftInverse _ _
  right_inv := doubleOfSum_doubleToSum_rightInverse _ _


@[ext]
protected theorem ext (Ty: Type u) (tys: List (Type u)) (isum1 isum2: IterSum Ty tys) (req1: isum1.valIndex = isum2.valIndex) (req2: isum1.val ≍ isum2.val) : isum1 = isum2 := by
  rcases isum1 with _ | ⟨_,_,_,isum1⟩
  <;> rcases isum2 with _ | ⟨_,_,_,isum2⟩
  <;> simp at req1 req2
  · rw [req2]
  · simp
    exact IterSum.ext _ _ isum1 isum2 req1 req2



theorem ne_of_valIndex_ne (Ty: Type u) (tys: List (Type u)) (isum1 isum2: IterSum Ty tys) (req: isum1.valIndex ≠ isum2.valIndex) : isum1 ≠ isum2 := by
  intro lm1
  rewrite [lm1] at req
  exact req (Eq.refl _)

theorem valType_eq_head_of_valIndex_eq_zero {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) (req: isum.valIndex = 0) : isum.ValType = Ty := by
  rcases isum with _ | ⟨_,_,_,_⟩
  · dsimp
  · simp at req



def getFin? {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) (i: Fin isum.types.length) : Option isum.types[i] :=
  let ⟨i, lm1⟩ := i
  if h1: isum.valIndex = i then
    .some (h1 ▸ (isum.valType_eq_types_getElem ▸ isum.val))
  else
    .none

theorem getFin?_isSome_of_valIndex_eq {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) (i: Fin isum.types.length) (req: isum.valIndex = ↑i)
  : (isum.getFin? i).isSome = .true := by
  dsimp [getFin?]
  simp [req]

def getFin {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) (i: Fin isum.types.length) (req: isum.valIndex = ↑i) : isum.types[i] :=
  (isum.getFin? i).get (isum.getFin?_isSome_of_valIndex_eq i req)


def areEq (Ty: Type u) (tys: List (Type u)) (isum1 isum2: IterSum Ty tys) (iter: IterDecidableEq (Ty::tys)) : Bool :=
  match isum1, isum2, iter with
  | .ofVal _ _ v1, .ofVal _ _ v2, .cons _ _ _ _ => decide (v1 = v2)
  | .cons _ _ _ isum1, .cons _ _ _ isum2, .cons _ _ _ iter => areEq _ _ isum1 isum2 iter
  | .ofVal .., .cons .., _
  | .cons .., .ofVal .., _ => .false

theorem areEq_eq_true_iff_eq {Ty: Type u} {tys: List (Type u)} {isum1 isum2: IterSum Ty tys} {iter: IterDecidableEq (Ty::tys)}
  : (areEq Ty tys isum1 isum2 iter = .true) ↔ (isum1 = isum2) := by
  rcases isum1 with _ | ⟨_,_,_,isum1⟩
  <;> rcases isum2 with _ | ⟨_,_,_,isum2⟩
  <;> rcases iter with _ | ⟨_,_,_,iter⟩
  <;> (
    simp only [areEq]
    simp )
  exact areEq_eq_true_iff_eq

protected instance decidableEq (Ty: Type u) (tys: List (Type u)) [HasIterDecidableEq (Ty::tys)] : DecidableEq (IterSum Ty tys) :=
  fun isum1 isum2 => decidable_of_iff (areEq Ty tys isum1 isum2 (@HasIterDecidableEq.iterDecidableEq (Ty::tys) _) = .true) areEq_eq_true_iff_eq

--@[implicit_reducible]
def append (tys1: List (Type u)) {Ty2: Type u} {tys2: List (Type u)} (isum: IterSum Ty2 tys2) : let tys := tys1 ++ Ty2 :: tys2; IterSum (tys.head (by subst tys; simp)) tys.tail :=
  match tys1 with
  | [] => isum
  | [Ty1] => .cons Ty1 Ty2 tys2 isum
  | [Ty1₁, Ty1₂] => .cons Ty1₁ Ty1₂ (Ty2 :: tys2) (.cons Ty1₂ Ty2 tys2 isum)
  | Ty1₁::Ty1₂::Ty1₃::tys1 =>
    let dd := append (Ty1₂::Ty1₃::tys1) isum
    .cons Ty1₁ Ty1₂ _ dd



@[elab_as_elim]
def recSingle.{um}
  {motive: (Ty: Type u) → (IterSum Ty []) → Sort um}
  (ofVal: (Ty: Type u) → (v: Ty) → motive Ty (.ofVal Ty [] v))
  (Ty: Type u) (isum: IterSum Ty [])
  : motive Ty isum :=
  match isum with
  | .ofVal _ _ v => ofVal Ty v

@[elab_as_elim]
def recSingleOn.{um}
  {motive: (Ty: Type u) → (IterSum Ty []) → Sort um}
  {Ty: Type u} (isum: IterSum Ty [])
  (ofVal: (Ty: Type u) → (v: Ty) → motive Ty (.ofVal Ty [] v))
  : motive Ty isum :=
  recSingle ofVal Ty isum


theorem single_valIndex {Ty: Type u} (isum: IterSum Ty []) : isum.valIndex = 0 := by
  cases isum using recSingleOn
  dsimp

structure Indexed (Ty: Type u) (tys: List (Type u)) (vi: Nat) where
  iterSum: IterSum Ty tys
  valIndex_eq_mod: iterSum.valIndex = vi

end IterSum


end Nemonuri.TypeLists

end
