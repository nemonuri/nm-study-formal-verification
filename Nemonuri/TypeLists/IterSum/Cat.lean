module


public import Nemonuri.TypeLists.IterSum.TypeTable
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists.IterSum


structure CatBuilder.{u, u2, u3} (Ty: Type u) (tys: List (Type u)) (Dom: TypeInfo Ty tys → Type u2) (Cod: (ti: TypeInfo Ty tys) → (Dom ti) → TypeInfo Ty tys → Type u3) where
  hom (ti1 ti2: TypeInfo Ty tys) : (v: Dom ti1) → Cod ti1 v ti2



/-
structure CatContext.{u, u2, u3} (Ty: Type u) (tys: List (Type u)) where
  Dom: TypeInfo Ty tys → Type u2
  Cod: (ti: TypeInfo Ty tys) → (Dom ti) → TypeInfo Ty tys → Type u3

structure CatHom.{u, u2, u3} (Ty: Type u) (tys: List (Type u)) (cb: CatContext.{u, u2, u3} Ty tys) (ti1 ti2: TypeInfo Ty tys) where
  toFun: (v: cb.Dom ti1) → cb.Cod ti1 v ti2

structure CatBuilder.{u, u2, u3} (Ty: Type u) (tys: List (Type u)) extends toContext: CatContext.{u, u2, u3} Ty tys where
  toHom (ti1 ti2: TypeInfo Ty tys) : CatHom Ty tys toContext ti1 ti2
-/

universe u uh u1 u2

/-
structure CatHom (Ty: Type u) (tys: List (Type u)) (C1: TypeInfo Ty tys → Type u1) (C2: (ti1: TypeInfo Ty tys) → (C1 ti1) → TypeInfo Ty tys → Type u2) where
  hom (ti1 ti2: TypeInfo Ty tys) : (v: C1 ti1) → C2 ti1 v ti2

namespace CatHom


variable {Ty: Type u} {tys: List (Type u)} {C1: TypeInfo Ty tys → Type u1} {C2: (ti1: TypeInfo Ty tys) → (C1 ti1) → TypeInfo Ty tys → Type u2}

def Hom (_: CatHom Ty tys C1 C2) (ti1 ti2: TypeInfo Ty tys) : Type _ := (v: C1 ti1) → C2 ti1 v ti2


end CatHom
-/
structure CatStruct (Ty: Type u) (tys: List (Type u)) (Hom: TypeInfo Ty tys → TypeInfo Ty tys → Type uh) where
  id (ti: TypeInfo Ty tys) : Hom ti ti
  comp {ti1 ti2 ti3: TypeInfo Ty tys} : Hom ti1 ti2 → Hom ti2 ti3 → Hom ti1 ti3


structure IsCat (Ty: Type u) (tys: List (Type u)) (Hom: TypeInfo Ty tys → TypeInfo Ty tys → Type uh) (s: CatStruct Ty tys Hom) : Prop where
  id_comp (ti1 ti2: TypeInfo Ty tys) (f: Hom ti1 ti2) : s.comp (s.id ti1) f = f
  comp_id (ti1 ti2: TypeInfo Ty tys) (f: Hom ti1 ti2) : s.comp f (s.id ti2) = f
  assoc (ti1 ti2 ti3 ti4: TypeInfo Ty tys) (f1: Hom ti1 ti2) (f2: Hom ti2 ti3) (f3: Hom ti3 ti4) : s.comp (s.comp f1 f2) f3 = s.comp f1 (s.comp f2 f3)


structure Cat (Ty: Type u) (tys: List (Type u)) (Hom: TypeInfo Ty tys → TypeInfo Ty tys → Type uh) extends toStruct: CatStruct Ty tys Hom where
  valid: IsCat Ty tys Hom toStruct

namespace Cat

variable {Ty: Type u} {tys: List (Type u)} {Hom: TypeInfo Ty tys → TypeInfo Ty tys → Type uh}

@[reducible]
def category (cat: Cat Ty tys Hom) : CategoryTheory.Category (TypeInfo Ty tys) where
  Hom := Hom
  id := cat.id
  comp := cat.comp
  id_comp := cat.valid.id_comp _ _
  comp_id := cat.valid.comp_id _ _
  assoc := cat.valid.assoc _ _ _ _


structure SingleStruct (Hom: Type uh) where
  id: Hom
  comp: Hom → Hom → Hom

namespace SingleStruct

def toLastCatStruct (Ty: Type u) (Hom: Type uh) (ss: SingleStruct Hom) : CatStruct Ty [] (fun _ _ => Hom) where
  id _ := ss.id
  comp := ss.comp

end SingleStruct


structure Last (Ty: Type u) (Hom: Type uh) extends toStruct: SingleStruct Hom where
  valid: IsCat Ty [] (fun _ _ => Hom) (toStruct.toLastCatStruct Ty)

def toCat {Ty: Type u} {Hom: Type uh} (l: Last Ty Hom) : Cat Ty [] (fun _ _ => Hom) := ⟨l.toStruct.toLastCatStruct Ty, l.valid⟩




structure ConsStruct (Hom: Type uh) (Ty: Type u) (tys: List (Type u))
  (HomCol: TypeInfo Ty tys → Type uh) (HomRow: TypeInfo Ty tys → Type uh) (HomTail: TypeInfo Ty tys → TypeInfo Ty tys → Type uh) extends toSingle: SingleStruct Hom where
  tail: CatStruct Ty tys HomTail
  col (ti1: TypeInfo Ty tys) : HomCol ti1
  row (ti2: TypeInfo Ty tys) : HomRow ti2


namespace ConsStruct

variable {Hom: Type uh} {Ty2: Type u} {tys: List (Type u)}
         {HomCol: TypeInfo Ty2 tys → Type uh} {HomRow: TypeInfo Ty2 tys → Type uh} {HomTail: TypeInfo Ty2 tys → TypeInfo Ty2 tys → Type uh}

def ConsHom (_: ConsStruct Hom Ty2 tys HomCol HomRow HomTail) (Ty: Type u) : TypeInfo Ty (Ty2::tys) → TypeInfo Ty (Ty2::tys) → Type uh :=
  TypeInfo.consPi₂ (fun _ _ => Type uh) Hom HomCol HomRow HomTail

@[defeq]
theorem consHom_def {s: ConsStruct Hom Ty2 tys HomCol HomRow HomTail} {Ty: Type u}
  : s.ConsHom Ty = TypeInfo.consPi₂ (fun _ _ => Type uh) Hom HomCol HomRow HomTail :=
  rfl

theorem consHom_zero_zero (s: ConsStruct Hom Ty2 tys HomCol HomRow HomTail) {Ty: Type u} (tt: TypeTable Ty (Ty2::tys))
  : s.ConsHom Ty (tt.get 0) (tt.get 0) = Hom := by
  dsimp [consHom_def, TypeInfo.consPi₂]
  simp [tt.index_eq_val]

theorem consHom_zero_cons (s: ConsStruct Hom Ty2 tys HomCol HomRow HomTail) {Ty: Type u} (tt: TypeTable Ty (Ty2::tys)) (ti: TypeInfo Ty2 tys)
  : s.ConsHom Ty (tt.get 0) (ti.cons Ty) = HomRow ti := by
  dsimp [consHom_def, TypeInfo.consPi₂]
  simp [tt.index_eq_val]
  intro lm1
  simp [TypeInfo.cons] at lm1

theorem consHom_cons_zero (s: ConsStruct Hom Ty2 tys HomCol HomRow HomTail) {Ty: Type u} (tt: TypeTable Ty (Ty2::tys)) (ti: TypeInfo Ty2 tys)
  : s.ConsHom Ty (ti.cons Ty) (tt.get 0) = HomCol ti := by
  dsimp [consHom_def, TypeInfo.consPi₂]
  simp [tt.index_eq_val]
  intro lm1
  simp [TypeInfo.cons] at lm1

@[defeq]
theorem consHom_cons_cons (s: ConsStruct Hom Ty2 tys HomCol HomRow HomTail) {Ty: Type u} (ti1 ti2: TypeInfo Ty2 tys)
  : s.ConsHom Ty (ti1.cons Ty) (ti2.cons Ty) = HomTail ti1 ti2 := by
  dsimp [consHom_def, TypeInfo.consPi₂, TypeInfo.cons, TypeInfo.tail]


def toCatStruct (s: ConsStruct Hom Ty2 tys HomCol HomRow HomTail) (tt: TypeTable Ty (Ty2::tys)) : CatStruct Ty (Ty2::tys) (s.ConsHom Ty) where
  id ti := tt.consPi (fun ti0 => (s.ConsHom Ty) ti0 ti0) (cast (s.consHom_zero_zero tt).symm s.id) s.tail.id ti
  comp {ti1 ti2 ti3} hom1 hom2 :=
    --tt.consPi₂ (s.ConsHom Ty) (cast (s.consHom_zero_zero tt).symm s.id) (cast (s.consHom_cons_zero tt _) s.row)

--structure IsCat (Ty: Type u) (tys: List (Type u)) (Hom: TypeInfo Ty tys → TypeInfo Ty tys → Type uh) (s: CatStruct Ty tys Hom) : Prop where


end ConsStruct


end Cat

/-

  mod_eq (idx: ℕ) : Pi Ty tys idx idx = Pi Ty tys (idx % (tys.length + 1)) (idx % (tys.length + 1))
  id_comp (idx1 idx2: ℕ) (f: Pi Ty tys idx1 idx2) : s.comp (s.id idx1)
-/



end Nemonuri.TypeLists.IterSum


end
