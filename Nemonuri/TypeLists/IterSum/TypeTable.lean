module

public import Nemonuri.TypeLists.IterSum.Explicit
public import Nemonuri.TypeLists.NonemptyAll

@[expose] public section

set_option autoImplicit false


namespace Nemonuri.TypeLists.IterSum

universe u u2

def HasTypeInfo (Head: Type u) (tail: List (Type u)) : Prop := NonemptyAll (Head::tail)

@[defeq]
theorem hasTypeInfo_def {Head: Type u} {tail: List (Type u)} : HasTypeInfo Head tail = NonemptyAll (Head::tail) := rfl


namespace HasTypeInfo

variable {Ty: Type u} {tys: List (Type u)}

theorem cons_nonemptyAll (h: HasTypeInfo Ty tys) : NonemptyAll (Ty::tys) := h

theorem of_nonemptyAll (req: NonemptyAll (Ty::tys)) : HasTypeInfo Ty tys := req

theorem head_nonempty (h: HasTypeInfo Ty tys) : Nonempty Ty := h.cons_nonemptyAll.nonempty_head

theorem tail_nonemptyAll (h: HasTypeInfo Ty tys) : NonemptyAll tys := by
  dsimp [HasTypeInfo] at h
  rcases h
  assumption

theorem cons (v: Ty) {Ty2: Type u} (h: HasTypeInfo Ty2 tys) : HasTypeInfo Ty (Ty2::tys) := of_nonemptyAll (.cons _ _ v h.cons_nonemptyAll)


theorem tail {Ty2: Type u} (h: HasTypeInfo Ty (Ty2::tys)) : HasTypeInfo Ty2 tys := h.tail_nonemptyAll

def length (_: HasTypeInfo Ty tys) : Nat := tys.length + 1

@[defeq]
theorem length_def (h: HasTypeInfo Ty tys) : h.length = tys.length + 1 := rfl

def getTypeInfo {Ty tys} (h: HasTypeInfo Ty tys) (i: Nat) (req: i < h.length) : TypeInfo Ty tys :=
  match tys, i with
  | tys, 0 => .mk 0 Ty (by
    dsimp [hasTypeInfo_def] at h
    rcases h
    refine (.intro (.ofVal tys ?_))
    assumption )
  | [], i+1 => False.elim (by simp [length] at req)
  | Ty2::tys, i+1 =>
    have lm1 : i < h.tail.length := by
      dsimp [length] at ⊢ req
      simpa using req
    (h.tail.getTypeInfo i lm1).cons Ty

theorem getTypeInfo_index_eq {Ty tys} (h: HasTypeInfo Ty tys) {i: Nat} {req: i < h.length} : (h.getTypeInfo i req).index = i := by
  rcases i with _ | ⟨i⟩
  · unfold getTypeInfo
    dsimp
  · rcases tys with _ | ⟨Ty2, tys⟩
    · simp [length] at req
    · dsimp [getTypeInfo, TypeInfo.cons]
      rcases h with _ | ⟨_,_,_,h⟩
      dsimp [← hasTypeInfo_def] at h
      rw [h.getTypeInfo_index_eq]


def typeInfoToFinIndex (h: HasTypeInfo Ty tys) (ti: TypeInfo Ty tys) : Fin h.length := ti.finIndex

def typeInfoOfFinIndex (h: HasTypeInfo Ty tys) (i: Fin h.length) : TypeInfo Ty tys := h.getTypeInfo i.val i.is_lt

theorem typeInfoOfFinIndex_typeInfoToFinIndex_leftInvserse {Ty tys} (h: HasTypeInfo Ty tys) : Function.LeftInverse (h.typeInfoOfFinIndex) (h.typeInfoToFinIndex) := by
  rintro ⟨idx, ITy, ⟨esum⟩⟩
  dsimp [typeInfoToFinIndex, typeInfoOfFinIndex, TypeInfo.finIndex]
  rcases idx with _ | ⟨idx⟩
  · unfold getTypeInfo
    congr
    exact esum.type_eq_of_zero
  · rcases tys with _ | ⟨Ty2, tys⟩
    · rcases esum
    · rcases esum with _ | ⟨_,_,_,_,esum⟩
      rcases h with _ | ⟨_,_,_,h⟩
      have lm1 := typeInfoOfFinIndex_typeInfoToFinIndex_leftInvserse h
      dsimp [Function.LeftInverse] at lm1
      specialize lm1 esum.typeInfo
      dsimp [typeInfoToFinIndex, typeInfoOfFinIndex, TypeInfo.finIndex, Explicit.typeInfo] at lm1
      dsimp [getTypeInfo]
      rw [lm1]
      dsimp [TypeInfo.cons]


theorem typeInfoOfFinIndex_typeInfoToFinIndex_rightInverse {Ty tys} (h: HasTypeInfo Ty tys) : Function.RightInverse (h.typeInfoOfFinIndex) (h.typeInfoToFinIndex) := by
  rintro ⟨idx, lm1⟩
  dsimp [typeInfoToFinIndex, typeInfoOfFinIndex, TypeInfo.finIndex]
  apply Fin.ext
  dsimp
  dsimp [length] at lm1
  rcases idx with _ | ⟨idx⟩
  · unfold getTypeInfo
    dsimp
  · rcases tys with _ | ⟨Ty2, tys⟩
    · simp at lm1
    · dsimp [getTypeInfo, TypeInfo.cons]
      revert lm1
      simp
      intro lm1
      rcases h with _ | ⟨_,_,_,h⟩
      have lm2 := typeInfoOfFinIndex_typeInfoToFinIndex_rightInverse h ⟨idx, lm1⟩
      dsimp [typeInfoToFinIndex, typeInfoOfFinIndex, TypeInfo.finIndex] at lm2
      exact Fin.ext_iff.mp lm2


def equivToFinIndex (h: HasTypeInfo Ty tys) : (TypeInfo Ty tys) ≃ (Fin h.length) where
  toFun := h.typeInfoToFinIndex
  invFun := h.typeInfoOfFinIndex
  left_inv := h.typeInfoOfFinIndex_typeInfoToFinIndex_leftInvserse
  right_inv := h.typeInfoOfFinIndex_typeInfoToFinIndex_rightInverse


end HasTypeInfo

/-
abbrev TypeTable (Ty: Type u) (tys: List (Type u)) : Type _ := (i: Fin (tys.length + 1)) → { ti: TypeInfo Ty tys // ti.index = i.val }

@[defeq]
theorem typeTable_def {Ty: Type u} {tys: List (Type u)} : TypeTable Ty tys = ((i: Fin (tys.length + 1)) → { ti: TypeInfo Ty tys // ti.index = i.val }) := rfl
-/

structure TypeTable (Ty: Type u) (tys: List (Type u)) where
  get : Fin (tys.length + 1) → TypeInfo Ty tys
  index_eq_val (i: Fin (tys.length + 1)) : (get i).index = i.val


namespace TypeTable

variable {Ty: Type u} {tys: List (Type u)}

@[reducible]
def length (_: TypeTable Ty tys) : Nat := tys.length + 1

@[defeq]
theorem length_def {tt: TypeTable Ty tys} : tt.length = tys.length + 1 := rfl

instance (tt: TypeTable Ty tys) : NeZero (tt.length) where
  out := Nat.succ_ne_zero tys.length


def getX (tt: TypeTable Ty tys) (i: Fin tt.length) : { ti: TypeInfo Ty tys // ti.index = i.val } := ⟨tt.get i, tt.index_eq_val i⟩

variable (Ty tys) in
def ofGetX (f: (i: Fin (tys.length + 1)) → { ti: TypeInfo Ty tys // ti.index = i.val }) : TypeTable Ty tys where
  get i := (f i).val
  index_eq_val i := (f i).property


def equivGetX : (TypeTable Ty tys) ≃ ((i: Fin (tys.length + 1)) → { ti: TypeInfo Ty tys // ti.index = i.val }) where
  toFun tt := tt.getX
  invFun := ofGetX Ty tys


variable (Ty tys) in
instance subsingleton : Subsingleton (TypeTable Ty tys) where
  allEq := by
    rintro ⟨g1, lm1⟩ ⟨g2, lm2⟩
    simp [funext_iff]
    intro i
    specialize lm1 i
    specialize lm2 i
    exact TypeInfo.ext (lm1.trans lm2.symm)

def tailGet {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (i: Fin (tys.length + 1)) : TypeInfo Ty2 tys :=
  let ⟨i, lm1⟩ := i
  let ti := tt.get ⟨i+1, (by simp; exact lm1)⟩
  ti.tail (by subst ti; rw [tt.index_eq_val _]; dsimp; exact Nat.zero_lt_succ i)

theorem tailGet_index_eq_val {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (i: Fin (tys.length + 1))
  : (tt.tailGet i).index = i.val := by
  rcases i with ⟨i, lm1⟩
  dsimp [TypeInfo.tail, tailGet]
  rw [tt.index_eq_val _]
  dsimp

def tail {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) : TypeTable Ty2 tys where
  get := tailGet tt
  index_eq_val := tt.tailGet_index_eq_val


theorem hasTypeInfo {Ty tys} (tt: TypeTable Ty tys) : HasTypeInfo Ty tys := by
  dsimp [hasTypeInfo_def]
  rcases (tt.getX 0) with ⟨⟨idx, ITy, ⟨esum⟩⟩, lm2⟩
  dsimp at lm2
  subst lm2
  rcases esum with ⟨_,v⟩ | _
  refine .cons _ _ v ?_
  rcases lm3: tys with _ | ⟨Ty2, tys⟩
  · exact .nil
  · dsimp only [← hasTypeInfo_def]
    rewrite [lm3] at tt
    exact tt.tail.hasTypeInfo

def ofHasTypeInfo (req: HasTypeInfo Ty tys) : TypeTable Ty tys where
  get := req.typeInfoOfFinIndex
  index_eq_val := by
    rintro ⟨i, lm1⟩
    dsimp [HasTypeInfo.typeInfoOfFinIndex]
    exact req.getTypeInfo_index_eq


def equivHasTypeInfo : TypeTable Ty tys ≃ HasTypeInfo Ty tys where
  toFun tt := tt.hasTypeInfo
  invFun := ofHasTypeInfo
  left_inv := (fun _ => Subsingleton.elim _ _)


def cons (v: Ty) {Ty2: Type u} (tt: TypeTable Ty2 tys) : TypeTable Ty (Ty2::tys) :=
  equivHasTypeInfo tt |>.cons v |> equivHasTypeInfo.symm


def equivToFinIndex (tt: TypeTable Ty tys) : (TypeInfo Ty tys) ≃ (Fin tt.length) := tt.hasTypeInfo.equivToFinIndex


def InnerTypeOfFin (tt: TypeTable Ty tys) (i: Fin tt.length) : Type u := (tt.get i).InnerType


def consTypeInfoPi {Ty Ty2: Type u} {tys: List (Type u)} --(tt: TypeTable Ty (Ty2::tys))
  (ToType: (Ty: Type u) → (tys: List (Type u)) → (ti: TypeInfo Ty tys) → (v: ti.InnerType) → Sort u2)
  (v1: Ty) (v2: ToType Ty (Ty2::tys) (.ofVal v1 (Ty2::tys)) v1)
  (tipi: (ti: TypeInfo Ty2 tys) → (v: ti.InnerType) → ToType Ty2 tys ti v)
  (ti: TypeInfo Ty (Ty2::tys)) (v: ti.InnerType) : ToType Ty (Ty2::tys) ti v :=
  if h1: ti.index = 0 then
    v2 |> cast (by
      have lm1 := ti.innerType_eq_of_index_eq_zero h1
      congr
      · dsimp [TypeInfo.ofVal]
        rcases ti
        dsimp at v h1 lm1
        subst lm1 h1
        rfl
      · rcases ti with ⟨idx, ITy, ⟨esum⟩⟩
        dsimp at v h1 lm1
        subst lm1 h1
        rcases esum  )
  else
  match tys with
  | [] => False.elim (by)
  --(v: ToType Ty (Ty2::tys) (tt.get 0)) (tipi: (ti: TypeInfo Ty2 tys) → ToType Ty2 tys ti)
  --(ti: TypeInfo Ty (Ty2::tys)) : ToType Ty (Ty2::tys) ti :=


/-
def tailTypeInfoPi {Ty Ty2: Type u} {tys} (tt: TypeTable Ty (Ty2::tys))
  (ToType: (Ty: Type u) → (tys: List (Type u)) → TypeInfo Ty tys → Sort u2)
  (tipi: (ti: TypeInfo Ty (Ty2::tys)) → ToType Ty (Ty2::tys) ti)
  (ti: TypeInfo Ty2 tys) : ToType Ty2 tys ti :=
-/

/-
def consTypeInfoPi {Ty Ty2: Type u} {tys} (tt: TypeTable Ty (Ty2::tys))
  (ToType: (Ty: Type u) → (tys: List (Type u)) → TypeInfo Ty tys → Sort u2)
  (v: ToType _ _ (tt.get 0)) (tipi: (ti: TypeInfo Ty2 tys) → ToType _ _ ti)
  (ti: TypeInfo Ty (Ty2::tys)) : ToType _ _ ti :=
  match lm1: ti.index with
  | 0 => v |> cast (by
    congr
    refine TypeInfo.ext ?_
    rw [lm1, tt.index_eq_val _]
    dsimp)
  | i+1 =>
    let ti2 : TypeInfo Ty2 tys := ti.tail (by rw [lm1]; exact Nat.zero_lt_succ _)
    match lm2: ti2.index with
    | 0 =>
-/
    --let tt2 := tt.tail
    --consTypeInfoPi tt ToType (tipi)

--{Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (ToType: TypeInfo Ty2 tys → Sort u2) (pi: (ti: TypeInfo Ty2 tys) → ToType ti)


/-
def liftTypeInfoFun {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) {α: Sort*} (v: α) (tif: TypeInfo Ty2 tys → α) (ti: TypeInfo Ty (Ty2::tys)) : α :=
  if h1: ti.index = 0 then v else tif (ti.tail (Nat.pos_of_ne_zero h1))
-/

end TypeTable




--abbrev TypeMap (Ty: Type u) (tys: List (Type u)) (α: Sort u2) : Sort _ :=



namespace TypeInfo

def consFun {α: Sort*} (v: α) {Ty: Type u} {Ty2: Type u} {tys: List (Type u)} (tif: TypeInfo Ty2 tys → α) (ti: TypeInfo Ty (Ty2::tys)) : α :=
  if h1: ti.index = 0 then v else tif (ti.tail (Nat.pos_of_ne_zero h1))

def consPi (toType: (Ty: Type u) → (tys: List (Type u)) → TypeInfo Ty tys → Sort u2)
  {Ty: Type u} {Ty2: Type u} {tys: List (Type u)} [Nonempty Ty] (v: toType Ty (Ty2::tys) (.ofNonempty Ty (Ty2::tys)))
  (tif: (ti: TypeInfo Ty2 tys) → toType Ty2 tys ti)
  (ti: TypeInfo Ty (Ty2::tys)) : toType Ty (Ty2::tys) ti :=
  if h1: ti.index = 0 then
    v |> cast (by
      congr
      dsimp [ofNonempty]
      congr <;> (try exact h1.symm)
      exact ti.innerType_eq_of_index_eq_zero h1 |>.symm)
  else
    tif (ti.tail (Nat.pos_of_ne_zero h1))
    --let tiTail := ti.tail (Nat.pos_of_ne_zero h1)
    --let v := tif tiTail
/-
    let tiTail := ti.tail (Nat.pos_of_ne_zero h1)
    let v := tif tiTail
-/

/-
def consPi (Ty: Type u) (v: Ty) {Ty2: Type u} {tys: List (Type u)}
           (toType: TypeInfo Ty2 tys → Type u2) (tif: (ti: TypeInfo Ty2 tys) → toType ti)
           (ti: TypeInfo Ty (Ty2::tys)) : consFun Ty toType ti :=
  if h1: ti.index = 0 then
-/
--def liftTypeFun (f: Type u → Sort u2) {Ty: Type u} {tys: List (Type u)} (ti: TypeInfo Ty tys) : Sort u2 :=

/-
def consPi {Ty: Type u} {α: Sort*} (f: Ty → α) {Ty2: Type u} {tys: List (Type u)}
           (tif: TypeInfo Ty2 tys → α)
-/


end TypeInfo


/-
class TypeTable (Head: Type u) (tail: List (Type u)) : Prop where
  nonemptyAll: NonemptyAll (Head::tail)
-/

/-
namespace TypeTable

--variable {Ty: Type u} {tys: List (Type u)}

variable (Ty tys) in
def lengthAt [TypeTable Ty tys] : Nat := tys.length + 1

theorem tailAt (Ty Ty2: Type u) (tys: List (Type u)) [TypeTable Ty (Ty2::tys)] : TypeTable Ty2 tys where
  nonemptyAll := by
    rename_i lm1
    rcases lm1 with ⟨lm1⟩
    rcases lm1
    assumption


def getTypeInfoAt (Ty: Type u) (tys: List (Type u)) [TypeTable Ty tys] (i: Nat) (req: i < lengthAt Ty tys) : TypeInfo Ty tys :=
  match i with
  | 0 => .mk 0 Ty (by
      rename_i lm1
      rcases lm1 with ⟨lm1⟩
      rcases lm1
      refine .intro (.ofVal tys ?_)
      assumption )
  | i+1 =>
  match tys with
  | Ty2::tys =>
    have lm1 : TypeTable Ty2 tys := by
    --let ti : TypeInfo Ty2 tys := getTypeInfoAt Ty2 tys i _
    --Typein
/-
  match i, tys with
  | 0, tys => .mk 0 Ty (by
      rename_i lm1
      rcases lm1 with ⟨lm1⟩
      rcases lm1
      rename Ty => v
      refine .intro ?_
      exact .ofVal tys v )
  | i+1, [] => False.elim (by dsimp [lengthAt] at req)
  | i+1, Ty2::tys =>
    have lm1 : TypeTable Ty2 tys := tailOf Ty Ty2 tys
    let ti : TypeInfo Ty2 tys := getTypeInfo i (by simp)
    Type
-/


--def types [TypeTable Ty tys] :


end TypeTable
-/

/-
inductive HasTypeMap : Type u → List (Type u) → Prop where
  | single (Ty: Type u) : Explicit Ty 0 Ty [] → HasTypeMap Ty []
  | cons (Ty: Type u) (tail: List (Type u)) : Explicit Ty 0 Ty tail
-/

/-
def IterProdT (m: Type u → Type u2) (Ty: Type u) : List (Type u) → Type u2
  | [] => m Ty
  | Ty2::tys => (m Ty) × (IterProdT m Ty2 tys)

def TypeTable (Ty: Type u) (tys: List (Type u)) : Prop :=
  match tys with
  | [] => Nonempty (Explicit Ty 0 Ty [])
  | Ty2::tys => (Nonempty (Explicit Ty2 0 Ty2 tys)) ∧ (TypeTable Ty2 tys)
-/
  --(Explicit Ty2 0 Ty2 tys) × (TypeTable Ty2 tys)

/-
inductive TypeTable : Type u → List (Type u) → Type _ where
  | single (Ty: Type u) (ti: TypeInfo Ty []) : TypeTable Ty []
  | cons (Ty Ty2: Type u) (tail: List (Type u)) (ti: TypeInfo Ty2 tail) : TypeTable Ty2 tail →
-/

/-
mutual



end
-/

/-
def TypeTable (Ty: Type u) : List (Type u) → Type _
  | [] => Ty
  | Ty2::tys => Ty × (TypeTable Ty2 tys)

#print TypeTable
-/

/-
def TypeTable (Ty: Type u) : List (Type u) → Type _
  | [] => Explicit Ty 0 Ty []
  | Ty2::tys => Explicit Ty2
-/



namespace TypeTable



end TypeTable

/-
namespace TypeInfo

variable {Ty Ty2: Type u} {tys: List (Type u)}

def consFun {α: Sort u2} (f: Ty → α) (tif: TypeInfo Ty2 tys → α) (ti: TypeInfo Ty (Ty2::tys)) : α :=
  match ti with
  | .mk i Tye lm1 =>


end TypeInfo
-/

end Nemonuri.TypeLists.IterSum
