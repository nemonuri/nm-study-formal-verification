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



/-
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



end TypeTable




--abbrev TypeMap (Ty: Type u) (tys: List (Type u)) (α: Sort u2) : Sort _ :=



namespace TypeInfo

/-
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
-/
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
