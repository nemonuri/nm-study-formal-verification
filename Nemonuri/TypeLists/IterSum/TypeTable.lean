module

public import Nemonuri.TypeLists.IterSum.Explicit
public import Nemonuri.TypeLists.NonemptyAll
public import Batteries.Data.List.Basic
public import Nemonuri.Data.List.MapRange

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

variable (Ty) in
theorem of_nonempty [Nonempty Ty] : HasTypeInfo Ty [] := by
  rename_i lm1
  rcases lm1 with ⟨v⟩
  refine .cons Ty [] v ?_
  exact .nil

theorem tail_nonemptyAll (h: HasTypeInfo Ty tys) : NonemptyAll tys := by
  dsimp [HasTypeInfo] at h
  rcases h
  assumption

theorem cons (v: Ty) {Ty2: Type u} (h: HasTypeInfo Ty2 tys) : HasTypeInfo Ty (Ty2::tys) := of_nonemptyAll (.cons _ _ v h.cons_nonemptyAll)

theorem cons_nonempty (Ty: Type u) [Nonempty Ty] {Ty2: Type u} (h: HasTypeInfo Ty2 tys) : HasTypeInfo Ty (Ty2::tys) := by
  rename_i lm1
  rcases lm1 with ⟨v⟩
  exact h.cons v

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




theorem mapM (h: HasTypeInfo Ty tys) (m: Type u → Type u2) [Pure m] : HasTypeInfo (m Ty) (tys.map m) :=
  match h.cons_nonemptyAll with
  | .cons _ _ v tail => .cons _ _ (pure v) (go tys tail) |> of_nonemptyAll
  where
    go: (tys: List (Type u)) → NonemptyAll tys → NonemptyAll (tys.map m)
      | [], .nil => .nil
      | _::tys, .cons _ _ v tail => .cons _ _ (pure v) (go tys tail)


--theorem mapM₂ (h: HasTypeInfo Ty tys) (m₂: Type u × Type u → Type u2) : letI t := List.product (Ty::tys) (Ty::tys); HasTypeInfo (m₂ (Ty, Ty)) (t.tail.map m₂) :=


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

@[defeq]
theorem tail_length_eq_length_sub_one {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) : tt.tail.length = tt.length - 1 := by dsimp


theorem tail_get_index_eq_val {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (i: Fin tt.tail.length) : (tt.tail.get i).index = i.val := TypeTable.index_eq_val _ _


theorem innerType_eq_of_get_zero (tt: TypeTable Ty tys) : (tt.get 0).InnerType = Ty := (tt.get 0).innerType_eq_of_index_eq_zero (tt.index_eq_val 0)




theorem innerType_eq_dite (tt: TypeTable Ty tys) (i: Fin tt.length) : (tt.get i).InnerType = (if h1: i = 0 then Ty else tys[i.val - 1]'(by rcases i with ⟨i, lm1⟩; simp at ⊢ h1; dsimp [length] at lm1; omega)) := by
  cases i using Fin.succRecOn
  · dsimp
    exact innerType_eq_of_get_zero _
  · rename_i i lm_t
    clear lm_t
    rcases tys with _ | ⟨Ty2, tys⟩
    · exact i.elim0
    · dsimp at i ⊢
      rcases tys with _ | ⟨Ty3, tys⟩
      · dsimp at i
        revert i
        simp
        have lm1 := (tt.get 1).innerType_eq_of_index_ne_zero
        simp [tt.index_eq_val] at lm1
        exact lm1
      · dsimp at i
        have lm2 := (tt.get i.succ).innerType_eq_of_index_ne_zero
        simp [tt.index_eq_val] at lm2
        rcases i with ⟨i, lm1⟩
        simp at lm2 ⊢
        exact lm2



/-
theorem innerType_eq_of_get_succ {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (i: Fin tt.tail.length)
  : (tt.get i.succ).InnerType = tt.tail.
-/



  --have := TypeInfo.Innteq



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

variable (Ty) in
def consNonempty [Nonempty Ty] {Ty2: Type u} (tt: TypeTable Ty2 tys) : TypeTable Ty (Ty2::tys) :=
  equivHasTypeInfo tt |>.cons_nonempty Ty |> equivHasTypeInfo.symm

theorem consNonempty_tail [Nonempty Ty] {Ty2: Type u} (tt: TypeTable Ty2 tys) : (tt.consNonempty Ty).tail = tt := Subsingleton.elim _ _

@[defeq]
theorem consNonempty_length [Nonempty Ty] {Ty2: Type u} (tt: TypeTable Ty2 tys)
  : (tt.consNonempty Ty).length = tt.length + 1 := by
  dsimp [length_def]




def equivToFinIndex (tt: TypeTable Ty tys) : (TypeInfo Ty tys) ≃ (Fin tt.length) := tt.hasTypeInfo.equivToFinIndex


def InnerTypeOfFin (tt: TypeTable Ty tys) (i: Fin tt.length) : Type u := (tt.get i).InnerType

variable (Ty) in
def ofNonempty [Nonempty Ty] : TypeTable Ty [] := HasTypeInfo.of_nonempty Ty |> ofHasTypeInfo


theorem head_nonempty (tt: TypeTable Ty tys) : Nonempty Ty := tt.hasTypeInfo.head_nonempty


theorem tail_consNonempty {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) : letI := tt.head_nonempty; tt.tail.consNonempty Ty = tt := Subsingleton.elim _ _

def headOnly (tt: TypeTable Ty tys) : TypeTable Ty [] := have := tt.head_nonempty; ofNonempty Ty

def headTypeInfo (tt: TypeTable Ty tys) : TypeInfo Ty tys := have := tt.head_nonempty; .ofNonempty Ty tys

theorem headTypeInfo_eq_get0 (tt: TypeTable Ty tys) : tt.headTypeInfo = tt.get 0 := by
  apply TypeInfo.ext
  rw [tt.index_eq_val]
  dsimp [headTypeInfo, TypeInfo.ofNonempty]

/-
def next? (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : Option (TypeInfo Ty tys) := ti.finIndex.addNat? 1 |>.map (tt.get) --tt.get (ti.finIndex + 1)

def prev? (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : Option (TypeInfo Ty tys) :=
  if h1: ti.index = 0 then .none else .some
-/

def nextOrSelf (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : TypeInfo Ty tys :=
  let tii : Nat := ti.index + 1
  if h1: tii < tt.length then tt.get ⟨tii, h1⟩ else ti

def prevOrSelf (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : TypeInfo Ty tys := tt.get ⟨(ti.index - 1), (by
    have lm1 := ti.index_le_length |> Nat.le_iff_lt_add_one.mp
    exact Nat.sub_lt_of_lt lm1 )⟩

@[elab_as_elim]
def recOfHasTypeInfo.{um}
  {motive: TypeTable Ty tys → Sort um}
  (ofHasTypeInfo: (h: HasTypeInfo Ty tys) → motive (.ofHasTypeInfo h))
  (t: TypeTable Ty tys)
  : motive t :=
  ofHasTypeInfo t.hasTypeInfo |> cast (by
    congr
    exact Subsingleton.elim _ _)

@[elab_as_elim]
def recOfSingleCons.{um}
  {motive: (Ty: Type u) → (tys: List (Type u)) → TypeTable Ty tys → Sort um}
  (single: (Ty: Type u) → (_: Nonempty Ty) → motive Ty [] (.ofNonempty Ty))
  (cons: (Ty: Type u) → (_: Nonempty Ty) → (Ty2: Type u) → (tys: List (Type u)) → (tt: TypeTable Ty2 tys) → motive Ty2 tys tt → motive Ty (Ty2::tys) (.consNonempty Ty tt))
  (Ty: Type u) (tys: List (Type u)) (t: TypeTable Ty tys)
  : motive Ty tys t :=
  match tys with
  | [] => single Ty t.head_nonempty |> cast (by congr; exact Subsingleton.elim _ _)
  | Ty2::tys => cons Ty t.head_nonempty Ty2 tys t.tail (recOfSingleCons single cons Ty2 tys t.tail) |> cast (by congr; exact Subsingleton.elim _ _)

@[elab_as_elim]
def recOfSingleConsOn.{um}
  {motive: (Ty: Type u) → (tys: List (Type u)) → TypeTable Ty tys → Sort um}
  {Ty: Type u} {tys: List (Type u)} (t: TypeTable Ty tys)
  (single: (Ty: Type u) → (_: Nonempty Ty) → motive Ty [] (.ofNonempty Ty))
  (cons: (Ty: Type u) → (_: Nonempty Ty) → (Ty2: Type u) → (tys: List (Type u)) → (tt: TypeTable Ty2 tys) → motive Ty2 tys tt → motive Ty (Ty2::tys) (.consNonempty Ty tt))
  : motive Ty tys t :=
  recOfSingleCons single cons Ty tys t


def mapM (tt: TypeTable Ty tys) (m: Type u → Type u2) [Pure m] : TypeTable (m Ty) (tys.map m) := tt.hasTypeInfo.mapM m |> ofHasTypeInfo


theorem consNonempty_get_succ_innerType_eq (Ty: Type u) [Nonempty Ty] {Ty2: Type u} {tys : List (Type u)} (tt: TypeTable Ty2 tys) (i: Fin tt.length)
  : ((consNonempty Ty tt).get i.succ).InnerType = (tt.get i).InnerType := by
  simp [innerType_eq_dite]
  cases i using Fin.succRecOn with
  | zero => dsimp
  | succ _ i lm_t =>
    clear lm_t
    simp
    rcases tys with _ | ⟨Ty3, tys⟩
    · exact i.elim0
    · rcases tys with _ | ⟨Ty4, tys⟩
      · revert i
        simp
        intro lm1
        dsimp only [OfNat.ofNat, Fin.ofNat] at lm1
        rewrite [Fin.ext_iff] at lm1
        dsimp at lm1
        simp only [reduceCtorEq] at lm1
      · rcases i with ⟨i, lm1⟩
        dsimp


theorem consNonempty_get_succ_eq_cons (Ty: Type u) [Nonempty Ty] {Ty2: Type u} {tys : List (Type u)} (tt: TypeTable Ty2 tys) (i: Fin tt.length)
  : ((consNonempty Ty tt).get i.succ) = TypeInfo.cons Ty (tt.get i) := by
  apply TypeInfo.ext
  dsimp [TypeInfo.cons]
  simp [TypeTable.index_eq_val]

theorem consNonempty_get_eq_dite (Ty: Type u) [Nonempty Ty] {Ty2: Type u} {tys : List (Type u)} (tt: TypeTable Ty2 tys) (i: Fin (tt.length + 1))
  : ((consNonempty Ty tt).get i) = if h1: i = 0 then (TypeInfo.ofNonempty Ty (Ty2::tys)) else TypeInfo.cons Ty (tt.get (i.pred h1)) := by
  cases i using Fin.succRecOn
  · dsimp
    apply TypeInfo.ext
    dsimp [TypeInfo.ofNonempty]
    exact index_eq_val _ _
  · rename_i i lm_t
    clear lm_t
    rw [consNonempty_get_succ_eq_cons]
    simp
    intro lm1
    rcases i with ⟨i, lm2⟩
    simp at lm1



theorem tail_get_innerType_eq_succ {Ty tys} {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (i: Fin tt.tail.length)
  : (tt.tail.get i).InnerType = (tt.get i.succ).InnerType := by
  cases i using Fin.succRecOn with
  | zero =>
    simp [innerType_eq_of_get_zero]
    have lm1 := tt.index_eq_val 1
    have lm2 := (tt.get 1).innerType_eq_of_index_ne_zero
    simp [lm1] at lm2
    exact lm2.symm
  | succ _ i lm_t =>
    clear lm_t
    cases tt using recOfSingleConsOn
    rename_i tt lm_t
    clear lm_t
    simp [consNonempty_tail]
    symm
    exact consNonempty_get_succ_innerType_eq Ty tt i.succ


theorem tail_get_eq_tail {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (i: Fin tt.tail.length)
  : (tt.tail.get i) = (tt.get i.succ).tail (by simp [index_eq_val]) := by
  apply TypeInfo.ext
  dsimp [TypeInfo.tail]
  simp [TypeTable.index_eq_val]

    --simp [consNonempty, equivHasTypeInfo]
    --generalize lm1: consNonempty Ty tt = tt2
    --generalize lm2: i.succ = i2




--def prev (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : TypeInfo Ty tys := tt.get (ti.finIndex - 1)

/-
theorem prev_next_leftInverse (tt: TypeTable Ty tys) : Function.LeftInverse tt.prev tt.next := by
  intro ti
  cases ti using TypeInfo.recOfNonemptyConsOn
  · dsimp [TypeInfo.ofNonempty, next, prev]
    apply TypeInfo.ext
    dsimp [TypeInfo.finIndex]
    simp [tt.index_eq_val]
  ·
-/
/-
  rintro ⟨idx, ITy, ⟨esum⟩⟩
  apply TypeInfo.ext
  dsimp [next, prev, TypeInfo.finIndex]
  simp [tt.index_eq_val]
  dsimp [Fin.add_def, Fin.sub_def]
  simp
-/
  --have := tt.equivToFinIndex.congr
/-
  dsimp [next, prev]
  apply TypeInfo.ext
  dsimp [TypeInfo.finIndex]
  simp [tt.index_eq_val]
  rcases
-/


def consPi {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (m: TypeInfo Ty (Ty2::tys) → Type u2) (v: m (tt.get 0))
  (tif: (ti: TypeInfo Ty2 tys) → m (ti.cons Ty))
  (ti: TypeInfo Ty (Ty2::tys)) : m ti :=
  if h1: ti.index = 0 then
    v |> cast (by congr; apply TypeInfo.ext; rw [h1, tt.index_eq_val]; dsimp)
  else
    tif (ti.tail (Nat.pos_of_ne_zero h1)) |> cast (by congr; exact ti.tail_cons _)


def consPi₂ {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (m₂: TypeInfo Ty (Ty2::tys) → TypeInfo Ty (Ty2::tys) → Type u2)
  (v: m₂ (tt.get 0) (tt.get 0)) (vcol: (ti: TypeInfo Ty2 tys) → m₂ (ti.cons Ty) (tt.get 0)) (vrow: (ti: TypeInfo Ty2 tys) → m₂ (tt.get 0) (ti.cons Ty))
  (tif₂: (ti1 ti2: TypeInfo Ty2 tys) → m₂ (ti1.cons Ty) (ti2.cons Ty))
  (ti1 ti2: TypeInfo Ty (Ty2::tys)) : m₂ ti1 ti2 :=
  if h1: ti1.index = 0 then
    if h2: ti2.index = 0 then
      v |> cast (by
        congr <;> apply TypeInfo.ext
        · rw [h1, tt.index_eq_val]; dsimp
        · rw [h2, tt.index_eq_val]; dsimp )
    else
      vrow (ti2.tail (Nat.pos_of_ne_zero h2)) |> cast (by
        congr
        · apply TypeInfo.ext
          rw [h1, tt.index_eq_val]; dsimp
        · exact ti2.tail_cons _ )
  else
    if h2: ti2.index = 0 then --rw [ti2.innerType_eq_of_index_eq_zero h2]; dsimp [tail]
      vcol (ti1.tail (Nat.pos_of_ne_zero h1)) |> cast (by
        congr
        · exact ti1.tail_cons _
        · apply TypeInfo.ext
          rw [h2, tt.index_eq_val]; dsimp )
    else
      tif₂ (ti1.tail (Nat.pos_of_ne_zero h1)) (ti2.tail (Nat.pos_of_ne_zero h2)) |> cast (by
        congr <;> exact TypeInfo.tail_cons _ _)


def consComp {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (m₂: TypeInfo Ty (Ty2::tys) → TypeInfo Ty (Ty2::tys) → Type u2)
  (v: m₂ (tt.get 0) (tt.get 0) → m₂ (tt.get 0) (tt.get 0) → m₂ (tt.get 0) (tt.get 0))
  (v_x: (ti1: TypeInfo Ty2 tys) → (m₂ (ti1.cons Ty) (tt.get 0)) → (m₂ (tt.get 0) (tt.get 0)) → m₂ (ti1.cons Ty) (tt.get 0))
  (v_y: (ti2: TypeInfo Ty2 tys) → (m₂ (tt.get 0) (ti2.cons Ty)) → (m₂ (ti2.cons Ty) (tt.get 0)) → (m₂ (tt.get 0) (tt.get 0)))
  (v_z: (ti3: TypeInfo Ty2 tys) → (m₂ (tt.get 0) (tt.get 0)) → (m₂ (tt.get 0) (ti3.cons Ty)) → (m₂ (tt.get 0) (ti3.cons Ty)))
  (v_xy: (ti1 ti2: TypeInfo Ty2 tys) → (m₂ (ti1.cons Ty) (ti2.cons Ty)) → (m₂ (ti2.cons Ty) (tt.get 0)) → m₂ (ti1.cons Ty) (tt.get 0))
  (v_xz: (ti1 ti3: TypeInfo Ty2 tys) → (m₂ (ti1.cons Ty) (tt.get 0)) → (m₂ (tt.get 0) (ti3.cons Ty)) → m₂ (ti1.cons Ty) (ti3.cons Ty))
  (v_yz : (ti2 ti3: TypeInfo Ty2 tys) → (m₂ (tt.get 0) (ti2.cons Ty)) → (m₂ (ti2.cons Ty) (ti3.cons Ty)) → m₂ (tt.get 0) (ti3.cons Ty))
  (tiComp: (ti1 ti2 ti3: TypeInfo Ty2 tys) → (m₂ (ti1.cons Ty) (ti2.cons Ty)) → (m₂ (ti2.cons Ty) (ti3.cons Ty)) → m₂ (ti1.cons Ty) (ti3.cons Ty))
  (ti1 ti2 ti3: TypeInfo Ty (Ty2::tys)) (hom1: m₂ ti1 ti2) (hom2: m₂ ti2 ti3) : m₂ ti1 ti3 :=
  have congr_m₂ {ti1 ti2 ti3 ti4: TypeInfo Ty (Ty2::tys)} (req1: ti1 = ti3) (req2: ti2 = ti4) : m₂ ti3 ti4 = m₂ ti1 ti2 := by congr <;> (symm; assumption)
  have index_zero {ti: TypeInfo Ty (Ty2::tys)} (req: ti.index = 0) : (tt.get 0) = ti := by apply TypeInfo.ext; rw [req]; exact tt.index_eq_val 0  --(tt.index_eq_val 0).trans req.symm
  if h1: ti1.index = 0 then
    have lm1 := index_zero h1
    if h2: ti2.index = 0 then
      have lm2 := index_zero h2
      if h3: ti3.index = 0 then
        have lm3 := index_zero h3
        v (cast (congr_m₂ lm1 lm2) hom1) (cast (congr_m₂ lm2 lm3) hom2) |> cast (congr_m₂ lm1.symm lm3.symm)
      else
        v_z (ti3.tail_of_ne_zero h3) (cast (congr_m₂ lm1 lm2) hom1) (cast (congr_m₂ lm2 (ti3.tail_cons _)) hom2) |> cast (congr_m₂ lm1.symm (ti3.tail_cons _).symm)
    else
      if h3: ti3.index = 0 then
        have lm3 := index_zero h3
        v_y (ti2.tail_of_ne_zero h2) (cast (congr_m₂ lm1 (ti2.tail_cons _)) hom1) (cast (congr_m₂ (ti2.tail_cons _) lm3) hom2) |> cast (congr_m₂ lm1.symm lm3.symm)
      else
        v_yz (ti2.tail_of_ne_zero h2) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ lm1 (ti2.tail_cons _)) hom1) (cast (congr_m₂ (ti2.tail_cons _) (ti3.tail_cons _)) hom2) |> cast (congr_m₂ lm1.symm (ti3.tail_cons _).symm)
  else
    if h2: ti2.index = 0 then
      have lm2 := index_zero h2
      if h3: ti3.index = 0 then
        have lm3 := index_zero h3
        v_x (ti1.tail_of_ne_zero h1) (cast (congr_m₂ (ti1.tail_cons _) lm2) hom1) (cast (congr_m₂ lm2 lm3) hom2) |> cast (congr_m₂ (ti1.tail_cons _).symm lm3.symm)
      else
        v_xz (ti1.tail_of_ne_zero h1) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ (ti1.tail_cons _) lm2) hom1) (cast (congr_m₂ lm2 (ti3.tail_cons _)) hom2) |> cast (congr_m₂ (ti1.tail_cons _).symm (ti3.tail_cons _).symm)
    else
      if h3: ti3.index = 0 then
        have lm3 := index_zero h3
        v_xy (ti1.tail_of_ne_zero h1) (ti2.tail_of_ne_zero h2) (cast (congr_m₂ (ti1.tail_cons _) (ti2.tail_cons _)) hom1) (cast (congr_m₂ (ti2.tail_cons _) lm3) hom2) |> cast (congr_m₂ (ti1.tail_cons _).symm lm3.symm)
      else
        tiComp (ti1.tail_of_ne_zero h1) (ti2.tail_of_ne_zero h2) (ti3.tail_of_ne_zero h3) (cast (congr_m₂ (ti1.tail_cons _) (ti2.tail_cons _)) hom1) (cast (congr_m₂ (ti2.tail_cons _) (ti3.tail_cons _)) hom2)
        |> cast (congr_m₂ (ti1.tail_cons _).symm (ti3.tail_cons _).symm)


structure WithMeta (Ty: Type u) (tys: List (Type u)) (ToMeta: (TypeInfo Ty tys) → Type*) extends toTypeTable: TypeTable Ty tys where
  getMeta (i: Fin (tys.length + 1)) : ToMeta (toTypeTable.get i)

end TypeTable

namespace TypeInfo

structure WithMeta (Ty: Type u) (tys: List (Type u)) (ToMeta: (TypeInfo Ty tys) → Type*) extends toTypeInfo: TypeInfo Ty tys where
  metadata: ToMeta toTypeInfo

structure GenericDef (Ty: Type u) (tys: List (Type u)) where
  arity: Nat
  eval: Vector (TypeInfo Ty tys) arity → Sort*

namespace GenericDef

variable {Ty: Type u} {tys: List (Type u)}

def isGenericType (gd: GenericDef Ty tys) : Bool := decide (0 < gd.arity)

end GenericDef

end TypeInfo

namespace TypeTable.WithMeta

variable {Ty: Type u} {tys: List (Type u)} (ToMeta: (TypeInfo Ty tys) → Type*)

def getWithMeta (ttm: WithMeta Ty tys ToMeta) (i: Fin ttm.length) : TypeInfo.WithMeta Ty tys ToMeta := ⟨ttm.get i, ttm.getMeta i⟩

end TypeTable.WithMeta

abbrev TypeTable.WithGenericDef (Ty: Type u) (tys: List (Type u)) : Type _ := TypeTable.WithMeta Ty tys (fun _ => TypeInfo.GenericDef Ty tys)


namespace TypeTable

variable {Ty: Type u} {tys: List (Type u)}

/-
def getByListRangeMem {tt: TypeTable Ty tys} (i: { i: Nat // i ∈ List.range tt.length }) : TypeInfo Ty tys :=
  tt.get ⟨i.val, (by revert i; simp)⟩
-/

--#check List.pmap

def range (tt: TypeTable Ty tys) : List (TypeInfo Ty tys) := --List.range tt.length |>.attach |>.map getByListRangeMem
  let ns := List.range tt.length
  ns.pmap (fun n lm1 => tt.get (Fin.mk n lm1)) (by subst ns; intro n; dsimp [length]; simp)


theorem range_ne_nil {tt: TypeTable Ty tys} : tt.range ≠ [] := by
  dsimp [range]
  simp

theorem pos_index_of_mem_of_range_tail {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys)) (ti: TypeInfo Ty (Ty2::tys)) (req: ti ∈ tt.range.tail)
  : 0 < ti.index := by
  dsimp [range] at req
  simp at req
  rcases req with ⟨idx, lm1, lm2⟩
  rw [← lm2]
  rcases lm1 with ⟨lm1, lm3⟩
  simp [index_eq_val]
  apply Nat.lt_of_add_one_le
  exact lm1

theorem range_single (tt: TypeTable Ty []) : tt.range = [tt.headTypeInfo] := by
  dsimp [range, length_def]
  rw [tt.headTypeInfo_eq_get0]



theorem consNonempty_range_eq (Ty: Type u) [Nonempty Ty] {Ty2: Type u} {tys: List (Type u)} (tt: TypeTable Ty2 tys)
  : (tt.consNonempty Ty).range = (TypeInfo.ofNonempty Ty (Ty2::tys))::(tt.range.map (fun ti => ti.cons Ty)) := by
  dsimp [range]
  simp [consNonempty_length, List.range_eq_cons_range'_1]
  refine ⟨?_, ?_⟩
  · apply TypeInfo.ext
    simp [index_eq_val]
    dsimp [TypeInfo.ofNonempty]
  · dsimp [length_def]
    simp [List.map_pmap]
    dsimp [List.range']
    simp
    simp [← consNonempty_get_succ_eq_cons]
    refine List.range'_pmap_congr 2 1 tys.length (fun s n => n < tys.length + s) _ _ _ _ ?_
    intro idx lm1
    apply TypeInfo.ext
    simp [index_eq_val]
    conv =>
      rhs
      rw [Nat.add_assoc]
      conv => rhs; rw [Nat.add_comm]
      rw [← Nat.add_assoc]



/-
    induction tys with
    | nil => simp
    | cons Ty3 tys lm1 =>
      dsimp
      simp [List.range'_1_concat]
-/
      --simp []
/-
    simp [consNonempty_get_eq_dite]
    dsimp [List.range']
    simp [← consNonempty_get_succ_eq_cons]
    simp [List.map_pmap]
    rcases tys with _ | ⟨Ty3, tys⟩
    · dsimp
    · simp
-/
/-
    cases tt using recOfSingleConsOn
    · simp [length_def]
      apply TypeInfo.ext
      dsimp [TypeInfo.cons]
      simp [index_eq_val]
    · rename_i Ty3 tys tt _ lm1_t
      clear lm1_t
      dsimp [consNonempty_length]
      have lm2 := consNonempty_range_eq Ty tt
      dsimp [range, consNonempty_length] at lm2
      simp [List.range_eq_cons_range'_1] at lm2
      rcases lm2 with ⟨lm2, lm3⟩
      clear lm2
-/
/-
      dsimp [range, consNonempty_length] at lm2
      simp [List.range_eq_cons_range'_1] at lm2
      rcases lm2 with ⟨lm3, lm4⟩
      exact lm4
-/

/-
    simp [List.map_pmap]
    dsimp [List.range']
    simp
    refine ⟨?_, ?_⟩
    · simp [consNonempty_get_eq_dite]
    · induction tys with
      | nil => dsimp
      | cons Ty3 tys lm1 =>
        dsimp [List.range']
        simp
-/
/-
  simp [List.map_pmap]
  simp [consNonempty_get_eq_dite]
-/



/-
  conv => lhs; dsimp [range, consNonempty_length]; simp [List.range_add]
  conv => rhs; dsimp [range]; simp [List.range_add]; simp [← consNonempty_get_succ_eq_cons]
  conv => lhs; dsimp [length_def]
  rcases tys with _ | ⟨Ty3, tys⟩
  · simp
    apply TypeInfo.ext
    dsimp [TypeInfo.ofNonempty]
    exact index_eq_val _ _
  · simp [List.range_add, ← consNonempty_get_succ_eq_cons]
    cases tt using recOfSingleConsOn
    rename_i tt lm1_t
    clear lm1_t
    have lm1 := consNonempty_range_eq Ty2 tt
-/







/-
theorem consNonempty_range_tail_eq_range_map_cons (Ty: Type u) [Nonempty Ty] {Ty2: Type u} {tys: List (Type u)} (tt: TypeTable Ty2 tys)
  : (tt.consNonempty Ty).range.tail = tt.range.map (fun ti => ti.cons Ty) := by
  conv => lhs; dsimp [range, consNonempty_length]; simp
  cases tt using recOfSingleConsOn
  · dsimp [length_def]
    simp [range_single]
    have lm1 := (ofNonempty Ty2).consNonempty_get_succ_eq_cons Ty 0
    dsimp at lm1
    rw [lm1, headTypeInfo_eq_get0]
  · rename_i Ty3 tys tt _ lm_t
    clear lm_t
-/




/-
theorem tail_range_eq_range_tail_pmap_tail {Ty tys} {Ty2: Type u} (tt: TypeTable Ty (Ty2::tys))
  : tt.tail.range = tt.range.tail.pmap (fun ti req => ti.tail req) (tt.pos_index_of_mem_of_range_tail) := by
  cases tt using recOfSingleConsOn
  rename_i tt lm_t
  clear lm_t
  simp [tt.consNonempty_tail]
  cases tt using recOfSingleConsOn
  · simp [range_single]
    dsimp [range, length_def]
    simp
    generalize (ofNonempty Ty2) = tt
    have lm1 := tt.consNonempty_get_succ_eq_cons Ty 0
    dsimp at lm1
    simp [lm1]
    exact tt.headTypeInfo_eq_get0
  · rename_i Ty3 tys tt _ lm_t
    clear lm_t
    generalize lm1: (consNonempty Ty2 tt) = tt2
    have lm2 := tail_range_eq_range_tail_pmap_tail tt2
    rewrite [Eq.comm] at lm1
    subst lm1
    simp [tt.consNonempty_tail] at lm2
    conv => lhs; dsimp [range, consNonempty_length]; simp [List.range_add]
    rw [← List.reverse_inj, List.reverse_append]
    simp
-/
    --rw [List.reveeq]



  --conv => lhs; dsimp [range]





--variable (Ty) in
/-
theorem range_eq_tail_cons (Ty: Type u) [Nonempty Ty] (tys: List (Type u)) (Ty2: Type u) (tt: TypeTable Ty (Ty2::tys))
  : tt.range = (TypeInfo.ofNonempty Ty (Ty2::tys))::(tt.tail.range.map (fun ti => ti.cons Ty)) := by
  generalize lm1: tt.tail = tt2
  dsimp [range, length_def]
  simp [List.range_add]
  rcases tys with _ | ⟨Ty3, tys⟩
  · simp
    refine ⟨?_, ?_⟩
    · apply TypeInfo.ext
      dsimp [TypeInfo.ofNonempty]
      exact tt.index_eq_val _
    · apply TypeInfo.ext
      dsimp [TypeInfo.cons]
      simp [index_eq_val]
  · simp [List.range_add]
    dsimp [TypeInfo.cons]
    simp [index_eq_val]
-/
/-
    simp [List.range_add]
    have lm2 := tt2.head_nonempty
    have lm3 := range_eq_tail_cons Ty2 tys Ty3 tt2
    dsimp [range, length_def] at lm3
    simp [List.range_add] at lm3
    simp [lm3]
-/
/-


  have lm2 (i: Nat) : (i ∈ List.range tt.length) = (i < tt.length) := by simp
-/

  --generalize List.range tt.length = df
  --have (eq := lm2) dd := List.range tt.length
  --generalize lm2: (List.range tt.length) = dd
  --conv => lhs; dsimp [length]; rw [List.attach_map_val]
  --rw [List.attach_map_val ]
  --generalize lm2: List.range tt.length = dd
/-

  dsimp [TypeInfo.ofNonempty]
  cases tt using recOfHasTypeInfo
  rename_i lm2
  cases tt2 using recOfHasTypeInfo
  rename_i lm3
  dsimp [range]
  simp
  unfold Function.comp
  simp
-/
/-
  dsimp [length]

-/
/-
  dsimp [hasTypeInfo_def] at lm1
  rcases lm1 with _ | ⟨_,_,v,lm1⟩
  rcases tys with _ | ⟨Ty3,tys⟩
  · rcases lm1 with _ | ⟨_,_,v2,lm2⟩
    dsimp [range, TypeTable.length_def]
    simp
    generalize lm3: (List.range 2).attach = ls
    rcases ls with _ | ⟨l,ls⟩
    · simp at lm3
    · have := List.attach
-/
    --dsimp [List.attach, List.attachWith] at lm3
    --00dsimp [List.attach, List.attachWith]
/-
  dsimp [range]
  rcases lm1 with _ | ⟨_,_,v,lm1⟩
  dsimp [← hasTypeInfo_def] at lm1
  simp
  dsimp [length, ofHasTypeInfo, HasTypeInfo.typeInfoOfFinIndex, TypeTable.tail, TypeTable.tailGet]
  dsimp [HasTypeInfo.getTypeInfo]
  dsimp [TypeInfo.cons]
-/
  --dsimp [TypeInfo.cons, TypeTable.tail]
  --dsimp [TypeInfo.cons, Type.tail]
  --dsimp [length, List.range]
/-


  simp

-/
  --have := List.attach_map

  --dsimp [range, tail, length, tailGet]
  --simp
  --dsimp [TypeInfo.cons, TypeInfo.tail]




end TypeTable


end Nemonuri.TypeLists.IterSum

end
