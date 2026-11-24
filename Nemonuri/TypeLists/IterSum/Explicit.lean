module


public import Nemonuri.TypeLists.IterSum.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists.IterSum


universe u


/-
inductive IterSum.{u} : Type u → List (Type u) → Type _ where
  | ofVal (Head: Type u) (tail: List (Type u)) (v: Head) : IterSum Head tail
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (isum: IterSum Head2 tail) : IterSum Head1 (Head2::tail)
-/

inductive Explicit (Tye: Type u) : Nat → Type u → List (Type u) → Type _ where
  | ofVal (tail: List (Type u)) (v: Tye) : Explicit Tye 0 Tye tail
  | cons (i: Nat) (Head1 Head2: Type u) (tail: List (Type u)) : Explicit Tye i Head2 tail → Explicit Tye (i+1) Head1 (Head2::tail)

/-
inductive Explicit : Type u → List (Type u) → Nat → Type u → Type _ where
  | ofVal (Head: Type u) (tail: List (Type u)) (v: Head) : Explicit Head tail 0 Head
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (i: Nat) (Tyi: Type u) (iter: Explicit Head2 tail i Tyi) : Explicit Head1 (Head2::tail) (i+1) Tyi
-/
namespace Explicit

variable {Tye: Type u} {i: Nat} {Ty: Type u} {tys: List (Type u)}


def toImplicit {i Ty tys} (esum: Explicit Tye i Ty tys) : IterSum Ty tys :=
  match i, esum with
  | 0, .ofVal _ v => .ofVal Tye tys v
  | _+1, .cons _ _ Ty2 tys esum => .cons Ty Ty2 tys esum.toImplicit


@[defeq, simp]
theorem toImplicit_ofVal {v: Tye} : toImplicit (ofVal tys v) = (IterSum.ofVal Tye tys v) := rfl

@[defeq, simp]
theorem toImplicit_cons {Ty2: Type u} {e: Explicit Tye i Ty2 tys} : toImplicit (cons i Ty Ty2 tys e) = (IterSum.cons Ty Ty2 tys e.toImplicit) := rfl

theorem toImplicit_valIndex {Tye i Ty tys} (e: Explicit Tye i Ty tys) : e.toImplicit.valIndex = i := by
  rcases e with _ | ⟨_,_,_,_,e⟩
  · dsimp
  · simp
    exact e.toImplicit_valIndex

theorem toImplicit_valType {Tye i Ty tys} (e: Explicit Tye i Ty tys) : e.toImplicit.ValType = Tye := by
  rcases e with _ | ⟨_,_,_,_,e⟩
  · dsimp
  · dsimp
    exact e.toImplicit_valType

--(e: Explicit Tye i Ty tys)
theorem toImplicit_type_eq (e: Explicit Tye i Ty tys) : Explicit e.toImplicit.ValType e.toImplicit.valIndex Ty tys = Explicit Tye i Ty tys := by
  congr
  · exact e.toImplicit_valType
  · exact e.toImplicit_valIndex


def ofImplicit {Ty tys} (isum: IterSum Ty tys) : Explicit isum.ValType isum.valIndex Ty tys :=
  match isum with
  | .ofVal _ _ v => .ofVal tys v
  | .cons _ Ty2 tys isum => .cons isum.valIndex Ty Ty2 tys (.ofImplicit isum)

@[defeq, simp]
theorem ofImplicit_ofVal {v: Ty} : ofImplicit (.ofVal _ tys v) = .ofVal tys v := rfl

@[defeq, simp]
theorem ofImplicit_cons {Ty2: Type u} {isum: IterSum Ty2 tys} : ofImplicit (.cons Ty Ty2 tys isum) = cons isum.valIndex Ty Ty2 tys (.ofImplicit isum) := rfl



theorem ofImplicit_toImplicit_leftInverse {Tye i Ty tys} (e: Explicit Tye i Ty tys) : cast (e.toImplicit_type_eq) (ofImplicit e.toImplicit) = e := by
  rcases e with _ | ⟨_,_,_,_,e⟩
  · dsimp
  · dsimp
    rw [cast_eq_iff_heq]
    congr
    · exact e.toImplicit_valType
    · exact e.toImplicit_valIndex
    · refine heq_of_cast_eq ?_ ?_
      · exact e.toImplicit_type_eq
      · exact e.ofImplicit_toImplicit_leftInverse


/-
inductive Monadic (Ty: Type u) (tys: List (Type u)) : Type (u+1) → Type (u+1) → Type _ where
  | intro (Tye: Type u) (i: Nat) : Monadic Ty tys (Explicit Tye i Ty tys) (IterSum Ty tys)
-/

/-
inductive IsLiftableAt (Ty: Type u) (tys: List (Type u)) (TyL: Type u) : Nat → Prop where
  | zero (req: Ty = TyL) : IsLiftableAt Ty tys TyL 0
  | succ (i: Nat) (req1: i < tys.length) (req2: tys[i] = TyL) : IsLiftableAt Ty tys TyL (i+1)
-/

def val {i Ty tys} (esum: Explicit Tye i Ty tys) : Tye :=
  match i, esum with
  | 0, .ofVal _ v => v
  | _+1, .cons _ _ _ _ esum => esum.val


def liftFun (TyL: Type u) (α: Sort*) (f: TyL → α) (i: Nat) {Ty tys} (esum: Explicit TyL i Ty tys) : α := f esum.val

def liftPi (TyL: Type u) (toSort: TyL → Sort*) (pi: (v: TyL) → toSort v) (i: Nat) {Ty tys} (esum: Explicit TyL i Ty tys) : toSort esum.val := pi esum.val

@[defeq]
theorem liftFun_eq_val_toSort.{u2} (TyL: Type u) (i: Nat) (toSort: TyL → Sort u2) (esum: Explicit TyL i Ty tys)
  : liftFun TyL (Sort u2) toSort i esum = toSort esum.val :=
  rfl


def liftFun₂ (TyL1 TyL2: Type u) (α: Sort*) (f: TyL1 → TyL2 → α) (i1 i2: Nat) {Ty tys} (esum1: Explicit TyL1 i1 Ty tys) (esum2: Explicit TyL2 i2 Ty tys) : α :=
  let f2 := liftPi TyL1 _ f i1 esum1
  liftFun TyL2 α f2 i2 esum2

@[defeq]
theorem liftFun₂_def  (TyL1 TyL2: Type u) (α: Sort*) (f: TyL1 → TyL2 → α) (i1 i2: Nat) {Ty tys} (esum1: Explicit TyL1 i1 Ty tys) (esum2: Explicit TyL2 i2 Ty tys)
  : liftFun₂ _ _ α f i1 i2 esum1 esum2 = f esum1.val esum2.val := by
  dsimp [liftFun₂, liftPi, liftFun]


theorem explicit_type_eq_of_index_eq {i Ty tys} {Tye2: Type u} (esum1: Explicit Tye i Ty tys) (esum2: Explicit Tye2 i Ty tys) : Tye = Tye2 := by
  rcases i with _ | ⟨i⟩
  · rcases esum1
    rcases esum2
    rfl
  · rcases esum1 with _ | ⟨_,_,_,_,esum1⟩
    rcases esum2 with _ | ⟨_,_,_,_,esum2⟩
    exact explicit_type_eq_of_index_eq esum1 esum2

theorem type_eq_of_zero (esum: Explicit Tye 0 Ty tys) : Ty = Tye := by
  rcases esum
  rfl


theorem index_le_length {i Ty tys} (esum: Explicit Tye i Ty tys) : i ≤ tys.length := by
  rcases i with _ | ⟨i⟩
  · exact Nat.zero_le _
  · rcases esum with _ | ⟨_,_,_,_,esum⟩
    simp
    exact index_le_length esum

theorem type_eq_of_add_one {i Ty tys} (esum: Explicit Tye (i+1) Ty tys) : ∃(_: i < tys.length), tys[i] = Tye := by
  refine ⟨?_,?_⟩
  · have lm1 := esum.index_le_length
    omega
  · rcases esum with _ | ⟨_,_,_,_,esum⟩
    rcases i with _ | ⟨i⟩
    · dsimp
      exact esum.type_eq_of_zero
    · dsimp
      rcases esum.type_eq_of_add_one with ⟨_,lm1⟩
      exact lm1

def tail {Ty2: Type u} : Explicit Tye (i+1) Ty (Ty2::tys) → Explicit Tye i Ty2 tys
  | .cons _ _ _ _ esum => esum

def ofGetElem (Ty tys) (i: Nat) (req1: i < tys.length) (v: tys[i]) : Explicit tys[i] (i+1) Ty tys :=
  match tys, i with
  | [], _ => False.elim (by simp at req1)
  | Ty2::tys, 0 => .cons 0 Ty Ty2 tys (.ofVal tys v)
  | Ty2::tys, i+1 =>
    have lm1 : i < tys.length := by simpa using req1
    .cons (i+1) Ty Ty2 tys (ofGetElem Ty2 tys i lm1 v)


theorem explicit_type_nonempty {i Ty tys} (esum: Explicit Tye i Ty tys) : Nonempty Tye := by
  rcases esum with _ | ⟨_,_,_,_,esum⟩
  · refine .intro ?_
    assumption
  · exact explicit_type_nonempty esum

theorem explicit_type_nonempty_of_nonempty (_: Nonempty (Explicit Tye i Ty tys)) : Nonempty Tye := by
  rename_i lm1
  rcases lm1 with ⟨esum⟩
  exact esum.explicit_type_nonempty


end Explicit

def toExplicit {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys) : Explicit isum.ValType isum.valIndex Ty tys := .ofImplicit isum

theorem toImplicit_toExplicit_leftInverse {Ty: Type u} {tys: List (Type u)} (isum: IterSum Ty tys)
  : isum.toExplicit.toImplicit = isum := by
  dsimp [toExplicit]
  rcases isum with _ | ⟨_,_,_,isum⟩
  · dsimp
  · dsimp
    have lm1 := isum.toImplicit_toExplicit_leftInverse
    dsimp [toExplicit] at lm1
    rw [lm1]

@[elab_as_elim]
def recToImplicit.{u2}
  {motive: (Ty: Type u) → (tys: List (Type u)) → (IterSum Ty tys) → Sort u2}
  (toImplicit: (Tye: Type u) → (i: Nat) → (Ty: Type u) → (tys: List (Type u)) → (esum: Explicit Tye i Ty tys) → motive Ty tys esum.toImplicit)
  (Ty: Type u) (tys: List (Type u)) (isum: IterSum Ty tys)
  : motive Ty tys isum :=
  toImplicit _ _ _ _ (isum.toExplicit) |> cast (by rw [isum.toImplicit_toExplicit_leftInverse])


def recToImplicitOn.{u2}
  {motive: (Ty: Type u) → (tys: List (Type u)) → (IterSum Ty tys) → Sort u2}
  {Ty tys} (isum: IterSum Ty tys)
  (toImplicit: (Tye: Type u) → (i: Nat) → (Ty: Type u) → (tys: List (Type u)) → (esum: Explicit Tye i Ty tys) → motive Ty tys esum.toImplicit)
  : motive Ty tys isum :=
  recToImplicit toImplicit Ty tys isum


theorem valType_eq_of_explicit_valIndex {Ty tys Tye} (isum: IterSum Ty tys) (esum: Explicit Tye isum.valIndex Ty tys) : isum.ValType = Tye := by
  cases isum using recToImplicitOn
  rename_i Tye2 i esum2
  rw [esum2.toImplicit_valType]
  rewrite [esum2.toImplicit_valIndex] at esum
  exact Explicit.explicit_type_eq_of_index_eq esum2 esum

--theorem valType_eq_of_valIndex_eq {Ty tys Tye} (isum: IterSum Ty tys) (esum: Explicit Tye isum.valIndex Ty tys) :

theorem valType_eq_of_explicit_valIndex_eq {Ty tys Tye i} (isum: IterSum Ty tys) (esum: Explicit Tye i Ty tys) (req: isum.valIndex = i) : isum.ValType = Tye := by
  rewrite [← req] at esum
  exact valType_eq_of_explicit_valIndex isum esum


def liftExplicit {Tye i Ty tys} [Nonempty (Explicit Tye i Ty tys)] (isum: IterSum Ty tys) (req: isum.valIndex = i) : Explicit Tye i Ty tys :=
  isum.toExplicit |> cast (by
    rename_i lm1
    rcases lm1 with ⟨esum⟩
    have lm1 := valType_eq_of_explicit_valIndex_eq isum esum req
    rw [lm1, req] )

def liftExplicit? {Tye i Ty tys} [Nonempty (Explicit Tye i Ty tys)] (isum: IterSum Ty tys) : Option (Explicit Tye i Ty tys) :=
  if h1: isum.valIndex = i then .some (isum.liftExplicit h1) else .none

structure TypeInfo (Ty: Type u) (tys: List (Type u)) where
  index: Nat
  InnerType: Type u
  valid: Nonempty (Explicit InnerType index Ty tys)

structure Object (Ty: Type u) (tys: List (Type u)) where
  typeIndex: Nat
  InnerType: Type u
  innerValue: Explicit InnerType typeIndex Ty tys

namespace TypeInfo

variable {Ty: Type u} {tys: List (Type u)}

abbrev ExplicitObj (ti: TypeInfo Ty tys) : Type _ := Explicit ti.InnerType ti.index Ty tys

instance (ti: TypeInfo Ty tys) : Nonempty (ti.ExplicitObj) := ti.valid

instance (ti: TypeInfo Ty tys) : Nonempty (Explicit ti.InnerType ti.index Ty tys) := ti.valid

def castIterSum (ti: TypeInfo Ty tys) (isum: IterSum Ty tys) (req: isum.valIndex = ti.index) : ti.ExplicitObj :=
  isum.liftExplicit req

def castIterSum? (ti: TypeInfo Ty tys) (isum: IterSum Ty tys) : Option ti.ExplicitObj := isum.liftExplicit?

def ofVal {Ty: Type u} (v: Ty) (tys: List (Type u)) : TypeInfo Ty tys := .mk 0 Ty (.intro (.ofVal tys v))

def cons (Ty: Type u) {Ty2 tys} (ti: TypeInfo Ty2 tys) : TypeInfo Ty (Ty2::tys) :=
  .mk (ti.index + 1) ti.InnerType (by
    rcases ti.valid with ⟨esum⟩
    exact .intro (Explicit.cons ti.index Ty Ty2 tys esum))

def tail {Ty2: Type u} (ti: TypeInfo Ty (Ty2::tys)) (req: 0 < ti.index) : TypeInfo Ty2 tys :=
  .mk (ti.index - 1) ti.InnerType (by
    rcases ti with ⟨i, ITy, lm1⟩
    dsimp at req ⊢
    rcases i with _ | ⟨i⟩
    · simp at req
    · dsimp
      rcases lm1 with ⟨esum⟩
      exact .intro esum.tail)

def tail_of_ne_zero {Ty2: Type u} (ti: TypeInfo Ty (Ty2::tys)) (req: ti.index ≠ 0) : TypeInfo Ty2 tys := ti.tail (Nat.pos_of_ne_zero req)

@[defeq, simp]
theorem tail_of_ne_zero_def {Ty2: Type u} (ti: TypeInfo Ty (Ty2::tys)) (req: ti.index ≠ 0) : ti.tail_of_ne_zero req = ti.tail (Nat.pos_of_ne_zero req) := rfl

@[simp]
theorem tail_cons {Ty2: Type u} (ti: TypeInfo Ty (Ty2::tys)) (req: 0 < ti.index) : (ti.tail req).cons Ty = ti := by
  dsimp [tail, cons]
  rcases ti with ⟨_,_,_⟩
  simp at ⊢ req
  exact Nat.sub_one_add_one (Nat.ne_zero_of_lt req)


theorem cons_index_pos {Ty2} (ti: TypeInfo Ty2 tys) : 0 < (ti.cons Ty).index := by
  dsimp [cons]
  exact Nat.add_one_pos _

@[defeq, simp]
theorem cons_tail {Ty2: Type u} (ti: TypeInfo Ty2 tys) : (ti.cons Ty).tail (ti.cons_index_pos) = ti := by
  dsimp [tail, cons]


def ofNonempty (Ty: Type u) [Nonempty Ty] (tys: List (Type u)) : TypeInfo Ty tys := .mk 0 Ty (by
    rename_i lm1
    rcases lm1 with ⟨v⟩
    exact .intro (.ofVal tys v))

theorem innerType_eq_of_index_eq_zero (ti: TypeInfo Ty tys) (req: ti.index = 0) : ti.InnerType = Ty := by
  rcases ti with ⟨idx, Tyi, ⟨elem⟩⟩
  dsimp at req ⊢
  subst req
  exact elem.type_eq_of_zero.symm


theorem index_le_length (ti: TypeInfo Ty tys) : ti.index ≤ tys.length := by
  rcases ti with ⟨idx, ITy, ⟨esum⟩⟩
  dsimp
  exact esum.index_le_length

theorem innerType_eq_of_index_ne_zero {Ty tys} (ti: TypeInfo Ty tys) (req: ti.index ≠ 0) : ti.InnerType = tys[ti.index - 1]'(by have := ti.index_le_length; omega) := by
  rcases ti with ⟨idx, ITy, ⟨esum⟩⟩
  dsimp at ⊢ req
  rcases esum with _ | ⟨idx,_,Ty2,tys,esum⟩
  · simp at req
  · dsimp
    rcases idx with _ | ⟨idx⟩
    · dsimp
      rcases esum
      rfl
    · dsimp
      let ti2 : TypeInfo Ty2 tys := .mk (idx+1) ITy (.intro esum)
      have lm1 : ti2.index ≠ 0 := by subst ti2; simp
      have lm2 := innerType_eq_of_index_ne_zero ti2 lm1
      subst ti2
      dsimp at lm1 lm2
      exact lm2


def finIndex (ti: TypeInfo Ty tys) : Fin (tys.length + 1) := .mk ti.index (Nat.lt_add_one_of_le ti.index_le_length)

@[ext]
protected theorem ext {ti1 ti2: TypeInfo Ty tys} (req: ti1.index = ti2.index) : ti1 = ti2 := by
  rcases ti1 with ⟨i1, Ty1, ⟨esum1⟩⟩
  rcases ti2 with ⟨i2, Ty2, ⟨esum2⟩⟩
  dsimp at req
  subst req
  congr
  exact Explicit.explicit_type_eq_of_index_eq esum1 esum2


instance : DecidableEq (TypeInfo Ty tys) := fun ti1 ti2 => decidable_of_iff' (ti1.index = ti2.index) (TypeInfo.ext_iff)


instance innerType_nonempty (ti: TypeInfo Ty tys) : Nonempty (ti.InnerType) := Explicit.explicit_type_nonempty_of_nonempty ti.valid


@[elab_as_elim]
def recOfNonemptyCons.{um}
  {motive: (Ty: Type u) → (tys: List (Type u)) → (TypeInfo Ty tys) → Sort um}
  (ofNonempty: (Ty: Type u) → (_: Nonempty Ty) → (tys: List (Type u)) → motive Ty tys (.ofNonempty Ty tys))
  (cons: (Ty Ty2: Type u) → (tys: List (Type u)) → (ti: TypeInfo Ty2 tys) → (motive Ty2 tys ti) → (motive Ty (Ty2::tys) (ti.cons Ty)))
  (Ty: Type u) (tys: List (Type u)) (ti: TypeInfo Ty tys)
  : motive Ty tys ti :=
  if h1: ti.index = 0 then
    ofNonempty ti.InnerType (ti.innerType_nonempty) tys |> cast (by
      have lm1 := ti.innerType_eq_of_index_eq_zero h1
      rcases ti with ⟨_,_,_⟩
      dsimp at lm1 h1 ⊢
      subst lm1 h1
      dsimp [TypeInfo.ofNonempty] )
  else
  match tys with
  | [] => False.elim (by
    have lm1 := ti.index_le_length
    simp at lm1
    exact h1 lm1 )
  | Ty2::tys =>
    let ti2 := ti.tail (Nat.pos_of_ne_zero h1)
    cons Ty Ty2 tys ti2 (recOfNonemptyCons ofNonempty cons Ty2 tys ti2) |> cast (by
      congr
      subst ti2
      dsimp [TypeInfo.cons, TypeInfo.tail]
      congr
      exact Nat.sub_one_add_one h1 )

@[elab_as_elim]
def recOfNonemptyConsOn.{um}
  {motive: (Ty: Type u) → (tys: List (Type u)) → (TypeInfo Ty tys) → Sort um}
  {Ty: Type u} {tys: List (Type u)} (ti: TypeInfo Ty tys)
  (ofNonempty: (Ty: Type u) → (_: Nonempty Ty) → (tys: List (Type u)) → motive Ty tys (.ofNonempty Ty tys))
  (cons: (Ty Ty2: Type u) → (tys: List (Type u)) → (ti: TypeInfo Ty2 tys) → (motive Ty2 tys ti) → (motive Ty (Ty2::tys) (ti.cons Ty)))
  : motive Ty tys ti :=
  recOfNonemptyCons ofNonempty cons Ty tys ti


def consFun {Ty2: Type u} {α: Sort*} (v: α) (tif: TypeInfo Ty2 tys → α) (ti: TypeInfo Ty (Ty2::tys)) : α :=
  if h1: ti.index = 0 then v else tif (ti.tail (Nat.pos_of_ne_zero h1))


def consPi.{u2} {Ty2: Type u} (m: Type u → Type u2) (v: m Ty)
  (tif: (ti: TypeInfo Ty2 tys) → m ti.InnerType) (ti: TypeInfo Ty (Ty2::tys)) : m ti.InnerType :=
  if h1: ti.index = 0 then
    v |> cast (by rw [ti.innerType_eq_of_index_eq_zero h1])
  else
    tif (ti.tail (Nat.pos_of_ne_zero h1))

def consPi₂.{u2} {Ty2: Type u} (m₂: Type u → Type u → Type u2)
  (v: m₂ Ty Ty) (vcol: (ti: TypeInfo Ty2 tys) → m₂ ti.InnerType Ty) (vrow: (ti: TypeInfo Ty2 tys) → m₂ Ty ti.InnerType)
  (tif₂: (ti1 ti2: TypeInfo Ty2 tys) → m₂ ti1.InnerType ti2.InnerType)
  (ti1 ti2: TypeInfo Ty (Ty2::tys)) : m₂ ti1.InnerType ti2.InnerType :=
  if h1: ti1.index = 0 then
    if h2: ti2.index = 0 then
      v |> cast (by rw [ti1.innerType_eq_of_index_eq_zero h1, ti2.innerType_eq_of_index_eq_zero h2])
    else
      vrow (ti2.tail (Nat.pos_of_ne_zero h2)) |> cast (by rw [ti1.innerType_eq_of_index_eq_zero h1]; dsimp [tail])
  else
    if h2: ti2.index = 0 then
      vcol (ti1.tail (Nat.pos_of_ne_zero h1)) |> cast (by rw [ti2.innerType_eq_of_index_eq_zero h2]; dsimp [tail])
    else
      tif₂ (ti1.tail (Nat.pos_of_ne_zero h1)) (ti2.tail (Nat.pos_of_ne_zero h2))

def consComp.{u2} {Ty2: Type u} (m₂: Type u → Type u → Type u2)
  (v: m₂ Ty Ty → m₂ Ty Ty → m₂ Ty Ty)
  (v_x: (ti1: TypeInfo Ty2 tys) → (m₂ ti1.InnerType Ty) → (m₂ Ty Ty) → m₂ ti1.InnerType Ty)
  (v_y: (ti2: TypeInfo Ty2 tys) → (m₂ Ty ti2.InnerType) → (m₂ ti2.InnerType Ty) → (m₂ Ty Ty))
  (v_z: (ti3: TypeInfo Ty2 tys) → (m₂ Ty Ty) → (m₂ Ty ti3.InnerType) → (m₂ Ty ti3.InnerType))
  (v_xy: (ti1 ti2: TypeInfo Ty2 tys) → (m₂ ti1.InnerType ti2.InnerType) → (m₂ ti2.InnerType Ty) → m₂ ti1.InnerType Ty)
  (v_xz: (ti1 ti3: TypeInfo Ty2 tys) → (m₂ ti1.InnerType Ty) → (m₂ Ty ti3.InnerType) → m₂ ti1.InnerType ti3.InnerType)
  (v_yz : (ti2 ti3: TypeInfo Ty2 tys) → (m₂ Ty ti2.InnerType) → (m₂ ti2.InnerType ti3.InnerType) → m₂ Ty ti3.InnerType)
  (tiComp: (ti1 ti2 ti3: TypeInfo Ty2 tys) → (m₂ ti1.InnerType ti2.InnerType) → (m₂ ti2.InnerType ti3.InnerType) → m₂ ti1.InnerType ti3.InnerType)
  (ti1 ti2 ti3: TypeInfo Ty (Ty2::tys)) (hom1: m₂ ti1.InnerType ti2.InnerType) (hom2: m₂ ti2.InnerType ti3.InnerType) : m₂ ti1.InnerType ti3.InnerType :=
  have congr_m₂ {Ty1 Ty2 Ty3 Ty4: Type u} (req1: Ty1 = Ty3) (req2: Ty2 = Ty4) : m₂ Ty1 Ty2 = m₂ Ty3 Ty4 := congrArg₂ m₂ req1 req2
  if h1: ti1.index = 0 then
    have lm1 := ti1.innerType_eq_of_index_eq_zero h1
    if h2: ti2.index = 0 then
      have lm2 := ti2.innerType_eq_of_index_eq_zero h2
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v (cast (congr_m₂ lm1 lm2) hom1) (cast (congr_m₂ lm2 lm3) hom2) |> cast (congr_m₂ lm1.symm lm3.symm)
      else
        v_z (ti3.tail_of_ne_zero h3) (cast (congr_m₂ lm1 lm2) hom1) (cast (congr_m₂ lm2 rfl) hom2) |> cast (congr_m₂ lm1.symm rfl)
    else
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v_y (ti2.tail_of_ne_zero h2) (cast (congr_m₂ lm1 rfl) hom1) (cast (congr_m₂ rfl lm3) hom2) |> cast (congr_m₂ lm1.symm lm3.symm)
      else
        v_yz (ti2.tail_of_ne_zero h2) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ lm1 rfl) hom1) hom2 |> cast (congr_m₂ lm1.symm rfl)
  else
    if h2: ti2.index = 0 then
      have lm2 := ti2.innerType_eq_of_index_eq_zero h2
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v_x (ti1.tail_of_ne_zero h1) (cast (congr_m₂ rfl lm2) hom1) (cast (congr_m₂ lm2 lm3) hom2) |> cast (congr_m₂ rfl lm3.symm)
      else
        v_xz (ti1.tail_of_ne_zero h1) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ rfl lm2) hom1) (cast (congr_m₂ lm2 rfl) hom2)
    else
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v_xy (ti1.tail_of_ne_zero h1) (ti2.tail_of_ne_zero h2) hom1 (cast (congr_m₂ rfl lm3) hom2) |> cast (congr_m₂ rfl lm3.symm)
      else
        tiComp (ti1.tail_of_ne_zero h1) (ti2.tail_of_ne_zero h2) (ti3.tail_of_ne_zero h3) hom1 hom2


/-
def consPi.{u2} {Ty2: Type u} (m: Type u → Type u2) (v: m Ty)
  (tif: (ti: TypeInfo Ty2 tys) → m ti.InnerType) (ti: TypeInfo Ty (Ty2::tys)) : m ti.InnerType :=
  if h1: ti.index = 0 then
    v |> cast (by rw [ti.innerType_eq_of_index_eq_zero h1])
  else
    tif (ti.tail (Nat.pos_of_ne_zero h1))

def consPi₂.{u2} {Ty2: Type u} (m₂: Type u → Type u → Type u2)
  (v: m₂ Ty Ty) (vcol: (ti: TypeInfo Ty2 tys) → m₂ ti.InnerType Ty) (vrow: (ti: TypeInfo Ty2 tys) → m₂ Ty ti.InnerType)
  (tif₂: (ti1 ti2: TypeInfo Ty2 tys) → m₂ ti1.InnerType ti2.InnerType)
  (ti1 ti2: TypeInfo Ty (Ty2::tys)) : m₂ ti1.InnerType ti2.InnerType :=
  if h1: ti1.index = 0 then
    if h2: ti2.index = 0 then
      v |> cast (by rw [ti1.innerType_eq_of_index_eq_zero h1, ti2.innerType_eq_of_index_eq_zero h2])
    else
      vrow (ti2.tail (Nat.pos_of_ne_zero h2)) |> cast (by rw [ti1.innerType_eq_of_index_eq_zero h1]; dsimp [tail])
  else
    if h2: ti2.index = 0 then
      vcol (ti1.tail (Nat.pos_of_ne_zero h1)) |> cast (by rw [ti2.innerType_eq_of_index_eq_zero h2]; dsimp [tail])
    else
      tif₂ (ti1.tail (Nat.pos_of_ne_zero h1)) (ti2.tail (Nat.pos_of_ne_zero h2))

def consComp.{u2} {Ty2: Type u} (m₂: Type u → Type u → Type u2)
  (v: m₂ Ty Ty → m₂ Ty Ty → m₂ Ty Ty)
  (v_x: (ti1: TypeInfo Ty2 tys) → (m₂ ti1.InnerType Ty) → (m₂ Ty Ty) → m₂ ti1.InnerType Ty)
  (v_y: (ti2: TypeInfo Ty2 tys) → (m₂ Ty ti2.InnerType) → (m₂ ti2.InnerType Ty) → (m₂ Ty Ty))
  (v_z: (ti3: TypeInfo Ty2 tys) → (m₂ Ty Ty) → (m₂ Ty ti3.InnerType) → (m₂ Ty ti3.InnerType))
  (v_xy: (ti1 ti2: TypeInfo Ty2 tys) → (m₂ ti1.InnerType ti2.InnerType) → (m₂ ti2.InnerType Ty) → m₂ ti1.InnerType Ty)
  (v_xz: (ti1 ti3: TypeInfo Ty2 tys) → (m₂ ti1.InnerType Ty) → (m₂ Ty ti3.InnerType) → m₂ ti1.InnerType ti3.InnerType)
  (v_yz : (ti2 ti3: TypeInfo Ty2 tys) → (m₂ Ty ti2.InnerType) → (m₂ ti2.InnerType ti3.InnerType) → m₂ Ty ti3.InnerType)
  (tiComp: (ti1 ti2 ti3: TypeInfo Ty2 tys) → (m₂ ti1.InnerType ti2.InnerType) → (m₂ ti2.InnerType ti3.InnerType) → m₂ ti1.InnerType ti3.InnerType)
  (ti1 ti2 ti3: TypeInfo Ty (Ty2::tys)) (hom1: m₂ ti1.InnerType ti2.InnerType) (hom2: m₂ ti2.InnerType ti3.InnerType) : m₂ ti1.InnerType ti3.InnerType :=
  have congr_m₂ {Ty1 Ty2 Ty3 Ty4: Type u} (req1: Ty1 = Ty3) (req2: Ty2 = Ty4) : m₂ Ty1 Ty2 = m₂ Ty3 Ty4 := congrArg₂ m₂ req1 req2
  if h1: ti1.index = 0 then
    have lm1 := ti1.innerType_eq_of_index_eq_zero h1
    if h2: ti2.index = 0 then
      have lm2 := ti2.innerType_eq_of_index_eq_zero h2
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v (cast (congr_m₂ lm1 lm2) hom1) (cast (congr_m₂ lm2 lm3) hom2) |> cast (congr_m₂ lm1.symm lm3.symm)
      else
        v_z (ti3.tail_of_ne_zero h3) (cast (congr_m₂ lm1 lm2) hom1) (cast (congr_m₂ lm2 rfl) hom2) |> cast (congr_m₂ lm1.symm rfl)
    else
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v_y (ti2.tail_of_ne_zero h2) (cast (congr_m₂ lm1 rfl) hom1) (cast (congr_m₂ rfl lm3) hom2) |> cast (congr_m₂ lm1.symm lm3.symm)
      else
        v_yz (ti2.tail_of_ne_zero h2) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ lm1 rfl) hom1) hom2 |> cast (congr_m₂ lm1.symm rfl)
  else
    if h2: ti2.index = 0 then
      have lm2 := ti2.innerType_eq_of_index_eq_zero h2
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v_x (ti1.tail_of_ne_zero h1) (cast (congr_m₂ rfl lm2) hom1) (cast (congr_m₂ lm2 lm3) hom2) |> cast (congr_m₂ rfl lm3.symm)
      else
        v_xz (ti1.tail_of_ne_zero h1) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ rfl lm2) hom1) (cast (congr_m₂ lm2 rfl) hom2)
    else
      if h3: ti3.index = 0 then
        have lm3 := ti3.innerType_eq_of_index_eq_zero h3
        v_xy (ti1.tail_of_ne_zero h1) (ti2.tail_of_ne_zero h2) hom1 (cast (congr_m₂ rfl lm3) hom2) |> cast (congr_m₂ rfl lm3.symm)
      else
        tiComp (ti1.tail_of_ne_zero h1) (ti2.tail_of_ne_zero h2) (ti3.tail_of_ne_zero h3) hom1 hom2
-/

end TypeInfo


/-
def liftExplicitFun {Tye i Ty tys} [Nonempty (Explicit Tye i Ty tys)] {α: Sort*} (f: Explicit Tye i Ty tys → α) (isum: IterSum Ty tys) (req: isum.valIndex = i) : α :=
  let esum : Explicit Tye i Ty tys := isum.toExplicit |> cast (by
    rcases (inferInstance: Nonempty (Explicit Tye i Ty tys)) with ⟨esum⟩
    rewrite [← req] at esum
    have lm1 := valType_eq_of_valIndex isum esum
    rw [lm1, req])
  f esum
-/
  --have lm1 : isum.ValType = Tye := by
  --if h1:



namespace Explicit

variable {Tye: Type u} {i: Nat} {Ty: Type u} {tys: List (Type u)}

def typeInfo (e: Explicit Tye i Ty tys) : TypeInfo Ty tys := .mk i Tye (.intro e)


end Explicit


/-
structure Box (Ty: Type u) (tys: List (Type u)) (i: Nat) where
  InnerType: Type u
  explicit: Explicit InnerType i Ty tys

/-- StateT 의 정의를 따라함. -/
@[implicit_reducible]
def BoxT.{u2, u3} (Ty: Type u) (tys: List (Type u)) (i: Nat) (m: Type u2 → Type u3) (boxToType: Box Ty tys i → Type u2) : Type (max (u+1) u3) :=
  (box: Box Ty tys i) → m (boxToType box)

@[reducible]
def BoxM.{u2} (Ty: Type u) (tys: List (Type u)) (i: Nat) (boxToType: Box Ty tys i → Type u2) : Type (max (u+1) u2) := BoxT Ty tys i Id boxToType
-/

end Nemonuri.TypeLists.IterSum

end
