module


public import Nemonuri.TypeLists.IterSum.TypeTable

@[expose] public section

set_option autoImplicit false


namespace Nemonuri.TypeLists.IterSum


universe u u2 u3


abbrev TypeInfoFun (Cod: Sort*) : Sort _ := ⦃Ty: Type u⦄ → ⦃tys: List (Type u)⦄ → (TypeInfo Ty tys) → Cod

abbrev TypeInfoPi (ToType: TypeInfoFun Sort*) : Sort _ := ⦃Ty: Type u⦄ → ⦃tys: List (Type u)⦄ → (ti: TypeInfo Ty tys) → ToType ti

namespace TypeTable


protected def TypeInfo {Ty: Type u} {tys: List (Type u)} (_: TypeTable Ty tys) : Type _ := TypeInfo Ty tys

/-
abbrev BiGeneric (m₂: ⦃Ty: Type u⦄ → ⦃tys: List (Type u)⦄ → (TypeInfo Ty tys) → (TypeInfo Ty tys) → Sort*) : Sort _ :=
  Generic (fun Ty tys ti => (ti2: TypeInfo Ty tys) → m₂ ti ti2)
-/

set_option genSizeOfSpec false in
inductive GenericDef {Ty: Type u} {tys: List (Type u)} (tt: TypeTable Ty tys) where
  | nil : Sort u2 → GenericDef tt
  | cons : (tt.TypeInfo → GenericDef tt) → GenericDef tt

abbrev GenericTypeFun {Ty: Type u} {tys: List (Type u)} (tt: TypeTable Ty tys) : Type _ := tt.TypeInfo → GenericDef tt

namespace GenericDef

variable {Ty: Type u} {tys: List (Type u)} {tt: TypeTable Ty tys}

variable (tt) in
def PredM (m: tt.TypeInfo → Sort*) (Pred: (ti: tt.TypeInfo) → m ti → Prop) : GenericDef tt :=
  let apply (ti: tt.TypeInfo) : GenericDef tt := .nil ((x: m ti) → Pred ti x)
  .cons apply

variable (tt) in
def RelM (m: tt.TypeInfo → Sort*) (Rel: (ti1 ti2: tt.TypeInfo) → m ti1 → m ti2 → Prop) : GenericDef tt :=
  let apply (ti1: tt.TypeInfo) : GenericDef tt := PredM tt m (fun ti2 x2 => (x1: m ti1) → Rel ti1 ti2 x1 x2)
  .cons apply


def maxArity (gd: GenericDef tt) : Nat :=
  match gd with
  | .nil _ => 0
  | .cons apply =>
    let nats : List Nat := tt.range.map (fun ti => apply ti |> maxArity)
    have lm1 : nats ≠ [] := by subst nats; simp; exact tt.range_ne_nil
    (nats.max lm1) + 1


def minArity (gd: GenericDef tt) : Nat :=
  match gd with
  | .nil _ => 0
  | .cons apply =>
    let nats : List Nat := tt.range.map (fun ti => apply ti |> minArity)
    have lm1 : nats ≠ [] := by subst nats; simp; exact tt.range_ne_nil
    (nats.min lm1) + 1


def isNil : GenericDef tt → Bool
  | .nil _ => .true
  | .cons _ => .false


def size (gd: GenericDef tt) : Nat :=
  match gd with
  | .nil _ => 1
  | .cons apply => tt.range.map (fun ti => apply ti |> size) |>.foldr (Nat.add) 1 --.foldl (Nat.add) 1

@[defeq]
theorem size_nil (S) : size (.nil S: GenericDef tt) = 1 := rfl

@[defeq]
theorem size_cons (app: GenericTypeFun tt) : size (cons app) = (tt.range.map (fun ti => app ti |> size) |>.foldr (Nat.add) 1) := rfl


theorem size_pos {tt: TypeTable Ty tys} (gd: GenericDef tt) : 0 < gd.size := by
  rcases gd with _ | ⟨apply⟩
  · dsimp [size]; exact Nat.zero_lt_one
  · dsimp [size]
    generalize lm1: tt.range = tis
    rcases tis with _ | ⟨ti,tis⟩
    · exact tt.range_ne_nil lm1 |>.elim
    · dsimp [List.map]
      apply Nat.lt_add_right
      exact size_pos _



def uniformArity? {tt: TypeTable Ty tys} (gd: GenericDef tt) : Option Nat :=
  match gd with
  | .nil _ => .some 0
  | .cons apply =>
  let gds : List (GenericDef tt) := tt.range.map (fun ti => apply ti)
  match h1: gds with
  | [] => False.elim (by subst gds; revert h1; simp; exact tt.range_ne_nil)
  | gd::gds =>
  let isNil0 : Bool := gd.isNil
  let allEq : Bool := gds.all (fun gd0 => gd0.isNil == isNil0)
  if !allEq then .none else
  let ua? : Option Nat := uniformArity? gd
  if isNil0 then ua?.map (Nat.succ) else
  match h2: ua? with
  | .none => .none
  | .some ua =>
  let isUniform : Bool := gds.attach.all (fun gd0 => decide (uniformArity? gd0.val = .some ua))
  if isUniform then .some (ua + 1) else .none
  termination_by gd.size
  decreasing_by
  · rename_i gds0 _
    subst gds0
    have lm2 := tt.range_ne_nil
    dsimp [size]
    generalize tt.range = tis at lm2 h1
    rcases tis with _ | ⟨ti,tis⟩ <;> simp at lm2
    clear lm2
    dsimp [List.map] at h1
    simp at h1
    rcases h1 with ⟨lm2, lm3⟩
    rewrite [Eq.comm] at lm2 lm3
    subst lm2
    dsimp [List.map]
    simp
    rcases tis with _ | _
    · dsimp [List.map]; exact Nat.zero_lt_one
    · dsimp [List.map]
      apply Nat.lt_add_right
      exact size_pos _
  · rename_i inv gds0 lm1 lm2
    revert gd0
    simp
    intro gd0 lm4
    dsimp [size_cons]
    subst gds0 isNil0 allEq ua?
    clear h2
    simp at lm1 lm2
    rewrite [lm2] at lm1
    specialize lm1 gd0 lm4
    cases tt using TypeTable.recOfSingleConsOn
    · dsimp [TypeTable.ofNonempty, TypeTable.range, TypeTable.length] at h1
      simp at h1
      dsimp [List.map] at h1
      simp at h1
      rcases h1 with ⟨lm5, lm6⟩
      subst lm6
      exact List.not_mem_nil lm4 |>.elim
    ·
/-

    rcases gd0 with ⟨gd0, lm3⟩
    dsimp [size]
    revert h2 lm1 lm2 inv
    simp [InvImage]
    intro inv lm2 lm1 h2
    rcases gd with _ | ⟨apply1⟩
    · dsimp [isNil] at lm2; simp only [Bool.true_eq_false] at lm2
    · generalize lm4: tt.range = tis
      revert h1
      simp [lm4]
      intro h1 h2
      rcases tis with _ | ⟨ti, tis⟩
      · exact tt.range_ne_nil lm4 |>.elim
      · dsimp [List.map] at ⊢ h1
        simp at h1
        rcases h1 with ⟨lm5, lm6⟩
        clear h2 h1
        rewrite [Eq.comm] at lm6
        subst lm6
        simp only [List.mem_map] at lm3
        rcases lm3 with ⟨ti2, lm3, lm6⟩
        rewrite [Eq.comm] at lm6
        subst lm6
        have lm6 := size_cons apply
-/
    --generalize lm4: tt.range = tis
    --clear h2
/-
      dsimp [size]
      generalize lm3: tt.range = tis
      rewrite [lm3] at h1
      rcases tis with _ | _
      · exact tt.range_ne_nil lm3 |>.elim
      · dsimp [List.map] at h1 ⊢
-/
/-
      conv => rhs; arg 2; rw [Nat.add_comm]
      subst lm3 isNil0 allEq
      rename_i lm1
      simp at lm1
      cases tis with
      | nil => dsimp [List.map]; simp
      | cons ti2 tis =>
        dsimp [List.map]
        simp at lm1
-/
/-
    rename_i gds0 lm1
    subst gds0 isNil0 allEq
    simp at lm1
    have lm2 := tt.range_ne_nil
    generalize lm4: tt.range = tis at lm2 h1
    rcases tis with _ | ⟨ti,tis⟩ <;> simp at lm2
    clear lm2
-/
/-

    dsimp [List.map] at h1
    simp at h1
    rcases h1 with ⟨lm2, lm3⟩
    rewrite [Eq.comm] at lm2 lm3
    subst lm2 lm3
    simp at lm1
-/





end GenericDef




namespace GenericTypeFun

--def Constructor


end GenericTypeFun


structure GenericType where
  apply (Ty: Type u) (tys: List (Type u)) : TypeTable Ty tys → TypeInfo Ty tys → Sort u2


structure Generic (gt: GenericType) where
  load (Ty: Type u) (tys: List (Type u)) (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : gt.apply Ty tys tt ti





/-
structure GenericDef (gt: GenericType) {Ty: Type u} {tys: List (Type u)} (tt: TypeTable Ty tys) where
  specialize (ti: TypeInfo Ty tys) : gt.apply Ty tys tt ti
-/

namespace GenericType

--def ExplicitRel₂ (Ty: Type u) (tys: List (Type u)) (ti: TypeInfo Ty tys) : GenericType where
--  apply

def ExplicitPred (tif: TypeInfoPi (fun _ _ ti => ti.ExplicitObj → Prop)) : GenericType where
  apply _ _ _ ti := (x: ti.ExplicitObj) → tif ti x

def Rel (m₂: ⦃Ty: Type u⦄ → ⦃tys: List (Type u)⦄ → (tt: TypeTable Ty tys) → (ti1 ti2: TypeInfo Ty tys) → ti1.InnerType → ti2.InnerType → Prop) : GenericType where
  apply Ty tys tt ti1 := (ti2: TypeInfo Ty tys) → (x1: ti1.InnerType) → (x2: ti2.InnerType) → m₂ tt ti1 ti2 x1 x2

end GenericType


/-
structure GenericFunc (fg: GenericType) where
  specialize (Ty: Type u) (tys: List (Type u)) (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : fg.apply Ty tys tt ti
-/




/-
structure GenericDef (fg: GenericType) where
  construct (Ty: Type u) (tys: List (Type u)) (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : fg.apply Ty tys tt ti
-/
namespace GenericType

def Ap (fg: GenericType) ⦃Ty: Type u⦄ ⦃tys: List (Type u)⦄ (tt: TypeTable Ty tys) (ti: TypeInfo Ty tys) : Sort u2 := fg.apply Ty tys tt ti

def Atom (fg: GenericType) (Ty: Type u) [Nonempty Ty] : Sort u2 := fg.Ap (.ofNonempty Ty) (.ofNonempty Ty [])

def atomToPi (fg: GenericType) (Ty: Type u) [Nonempty Ty] (atom: fg.Atom Ty) (ti: TypeInfo Ty []) : fg.Ap (.ofNonempty Ty) ti :=
  atom |> cast (by
    dsimp [GenericType.Atom]
    congr
    exact Subsingleton.elim _ _ )





structure PiConstructor (fg: GenericType) where
  equivTail (Ty2: Type u) (tys: List (Type u)) (tt: TypeTable Ty2 tys) (ti: TypeInfo Ty2 tys) (Ty: Type u) [Nonempty Ty]
    : (fg.Ap (tt.consNonempty Ty) (ti.cons Ty)) ≃ (fg.Ap tt ti)
  equivHead (Ty: Type u) (tys: List (Type u)) (tt: TypeTable Ty tys) : (fg.Ap tt tt.headTypeInfo) ≃ (@fg.Atom Ty tt.head_nonempty)

namespace PiConstructor

variable {fg: GenericType}

def head (ctor: fg.PiConstructor) {Ty: Type u} {tys: List (Type u)} (tt: TypeTable Ty tys) (pi: (ti: TypeInfo Ty tys) → fg.Ap tt ti) : @fg.Atom Ty tt.head_nonempty :=
  pi tt.headTypeInfo |> ctor.equivHead Ty tys tt

def tail (ctor: fg.PiConstructor) {Ty Ty2: Type u} {tys: List (Type u)} (tt: TypeTable Ty (Ty2::tys)) (pi: (ti: TypeInfo Ty (Ty2::tys)) → fg.Ap tt ti) (ti: TypeInfo Ty2 tys)
  : fg.Ap tt.tail ti :=
  have lm1 := tt.head_nonempty
  ctor.equivTail Ty2 tys tt.tail ti Ty (pi (ti.cons Ty) |> cast (by
    congr
    exact Subsingleton.elim _ _ ))

def single (_: fg.PiConstructor) (Ty: Type u) [Nonempty Ty] (atom: fg.Atom Ty) (ti: TypeInfo Ty []) : fg.Ap (.ofNonempty Ty) ti :=
  fg.atomToPi Ty atom ti

def cons  (ctor: fg.PiConstructor) (Ty: Type u) [Nonempty Ty] (Ty2: Type u) (tys: List (Type u))
          (atom: fg.Atom Ty) (tt: TypeTable Ty2 tys) (pi: (ti: TypeInfo Ty2 tys) → fg.Ap tt ti)
          (ti: TypeInfo Ty (Ty2::tys)) : fg.Ap (tt.consNonempty Ty) ti :=
  let tt2 := tt.consNonempty Ty
  let v := ctor.equivHead Ty (Ty2::tys) tt2 |>.symm atom
  let tif (ti: TypeInfo Ty2 tys) : fg.Ap tt2 (ti.cons Ty) := pi ti |> (ctor.equivTail Ty2 tys tt ti Ty).symm
  tt2.consPi (fun ti => fg.Ap tt2 ti) v tif ti

theorem cons_tail (ctor: fg.PiConstructor) (Ty: Type u) [Nonempty Ty] (Ty2: Type u) (tys: List (Type u)) (atom: fg.Atom Ty) (tt: TypeTable Ty2 tys) (pi: (ti: TypeInfo Ty2 tys) → fg.Ap tt ti)
  : ctor.tail (tt.consNonempty Ty) (ctor.cons Ty Ty2 tys atom tt pi) = cast (by rw [tt.consNonempty_tail]) pi := by
  apply eq_of_heq
  rw [heq_cast_iff_heq]
  unfold tail
  dsimp
  rw [tt.consNonempty_tail]
  apply heq_of_eq
  apply funext
  intro ti
  dsimp
  rw [← Equiv.eq_symm_apply]
  dsimp [cons, TypeTable.consPi, TypeInfo.cons]
  rcases ti with ⟨idx, ITy, lm1⟩
  dsimp [TypeInfo.tail]
  rfl

theorem head_tail_cons (ctor: fg.PiConstructor) {Ty Ty2: Type u} {tys: List (Type u)} (tt: TypeTable Ty (Ty2::tys)) (pi: (ti: TypeInfo Ty (Ty2::tys)) → fg.Ap tt ti)
  : letI := tt.head_nonempty; ctor.cons Ty Ty2 tys (ctor.head tt pi) tt.tail (ctor.tail tt pi) = cast (by rw [tt.tail_consNonempty]) pi := by
  apply eq_of_heq
  rw [heq_cast_iff_heq]
  unfold cons
  dsimp [consPi]
  refine Function.hfunext rfl ?_
  simp only [heq_eq_eq, forall_eq']
  intro ti
  cases tt using TypeTable.recOfHasTypeInfo
  rename_i lm1
  dsimp [TypeTable.consNonempty, equivHasTypeInfo]
  apply heq_of_eq
  cases ti using TypeInfo.recOfNonemptyConsOn with
  | ofNonempty =>
    dsimp [TypeInfo.ofNonempty]
    dsimp [head]
    symm
    apply eq_of_heq
    rw [heq_cast_iff_heq]
    dsimp [headTypeInfo, TypeInfo.ofNonempty]
    apply heq_of_eq
    have lm2 := (ctor.equivHead Ty (Ty2 :: tys) (ofHasTypeInfo lm1)).symm_apply_apply
    dsimp [headTypeInfo, TypeInfo.ofNonempty] at lm2
    symm
    exact lm2 _
  | cons _ _ _ ti lm_t =>
    clear lm_t
    split
    · rename_i lm2; simp [TypeInfo.cons] at lm2
    · simp
      dsimp [tail]
      have lm2 := lm1.head_nonempty
      have lm3 := (ctor.equivTail Ty2 tys (ofHasTypeInfo lm1).tail ti Ty).symm_apply_apply
      dsimp [consNonempty, equivHasTypeInfo] at ⊢ lm3
      exact lm3 _



end PiConstructor


end GenericType

/-
structure BiFreeGeneric where
  specialize (Ty: Type u) (tys: List (Type u)) : TypeTable Ty tys → TypeInfo Ty tys → FreeGeneric.{u, u2}


namespace BiFreeGeneric

def toFreeGeneric (bfg: BiFreeGeneric) : FreeGeneric where
  specialize Ty tys tt ti := (Ty0: Type u) → (tys0: List (Type u)) → (tt0: TypeTable Ty0 tys0) → (ti0: TypeInfo Ty0 tys0) → (bfg.specialize Ty tys tt ti).Ap tt0 ti0


end BiFreeGeneric
-/



structure FreeGenericHom (lg1: FreeGeneric.{u, u2}) (lg2: FreeGeneric.{u, u3}) where
  specialize (Ty: Type u) (tys: List (Type u)) (tt: TypeTable Ty tys) (ti1 ti2: TypeInfo Ty tys) : (lg1.Ap tt ti1) → (lg2.Ap tt ti2)


namespace FreeGenericHom

def Rel1 : FreeGeneric where
  specialize _ _ _ ti := ti.InnerType

def Rel2 : FreeGeneric where
  specialize _ _ _ ti :=

variable {lg1: FreeGeneric.{u, u2}} {lg2: FreeGeneric.{u, u3}}

def Ap₂ (lgh: FreeGenericHom lg1 lg2) ⦃Ty: Type u⦄ ⦃tys: List (Type u)⦄ (tt: TypeTable Ty tys) (ti1 ti2: TypeInfo Ty tys) : (lg1.Ap tt ti1) → (lg2.Ap tt ti2) :=
  lgh.specialize Ty tys tt ti1 ti2

end FreeGenericHom


structure FreeBiGeneric where
  specialize (Ty: Type u) (tys: List (Type u)) : TypeTable Ty tys → TypeInfo Ty tys → TypeInfo Ty tys → Sort u2

namespace FreeBiGeneric

def Ap₂ (lgh: FreeBiGeneric) ⦃Ty: Type u⦄ ⦃tys: List (Type u)⦄ (tt: TypeTable Ty tys) (ti1 ti2: TypeInfo Ty tys) : Sort u2 := lgh.specialize _ _ tt ti1 ti2

def Single (fbg: FreeBiGeneric) (Ty: Type u) [Nonempty Ty] : Sort _ := fbg.Ap₂ (.ofNonempty Ty []) (.ofNonempty Ty [])

def equivSinglePi (fbg: FreeBiGeneric) (Ty: Type u) [Nonempty Ty] : ((ti: TypeInfo Ty []) → fbg.Ap₂ ti ti) ≃ fbg.Single Ty where
  toFun pi := pi (.ofNonempty Ty [])
  invFun x := fun _ => x |> cast (by dsimp [Single]; congr <;> exact Subsingleton.elim _ _)
  left_inv := by
    intro pi1
    apply funext
    intro ti
    simp
    dsimp [TypeInfo.ofNonempty]
    apply eq_of_heq
    symm
    rw [heq_cast_iff_heq]
    congr
    apply TypeInfo.ext
    dsimp
    have lm1 := ti.index_le_length
    simpa using lm1

def cons (hce: FreeBiGeneric) (Ty: Type u) : FreeBiGeneric where
  specialize _ _ ti1 ti2 := hce.Ap₂ (ti1.cons Ty) (ti2.cons Ty)

universe u4

structure HomEquiv extends toFreeBiGeneric: FreeBiGeneric.{u, u2} where
  freeGeneric1: FreeGeneric.{u, u3}
  freeGeneric2: FreeGeneric.{u, u4}
  equiv (Ty: Type u) (tys: List (Type u)) (ti1 ti2: TypeInfo Ty tys) : (toFreeBiGeneric.Ap₂ ti1 ti2) ≃ ((freeGeneric1.Ap ti1) → (freeGeneric2.Ap ti2))

namespace HomEquiv

def Hom (he: HomEquiv) {Ty tys} (ti1 ti2: TypeInfo Ty tys) : Sort _ := he.Ap₂ ti1 ti2

end HomEquiv


structure HomCompEquiv extends toHomEquiv: HomEquiv.{u, u2, u3, u4} where
  compEquiv (Ty Ty2: Type u) (tys: List (Type u)) :
      ((ti1 ti2: TypeInfo Ty (Ty2::tys)) → toHomEquiv.Ap₂ ti1 ti2) ≃ (((ti: TypeInfo Ty []) → toHomEquiv.Ap₂ ti ti) ×' ((ti1 ti2: TypeInfo Ty2 tys) → toHomEquiv.Ap₂ ti1 ti2))
/-
  diagEquiv (Ty Ty2: Type u) (tys: List (Type u)) :
    ((ti: TypeInfo Ty (Ty2::tys)) → toHomEquiv.Ap₂ ti ti) ≃ (((ti: TypeInfo Ty []) → toHomEquiv.Ap₂ ti ti) ×' ((ti: TypeInfo Ty2 tys) → toHomEquiv.Ap₂ ti ti))
  consEquiv (Ty Ty2: Type u) (tys: List (Type u)) :
    ((ti1 ti2: TypeInfo Ty2 tys) → toHomEquiv.Ap₂ ti1 ti2) ≃ ((ti1 ti2: TypeInfo Ty2 tys) → toHomEquiv.Ap₂ (ti1.cons Ty) (ti2.cons Ty))
-/


namespace HomCompEquiv

variable {Ty Ty2: Type u} {tys: List (Type u)}


def head (hce: HomCompEquiv) (homPi: (ti1 ti2: TypeInfo Ty (Ty2::tys)) → hce.Ap₂ ti1 ti2) (ti: TypeInfo Ty []) : hce.Ap₂ ti ti :=
  (hce.compEquiv Ty Ty2 tys homPi).fst ti

def tail (hce: HomCompEquiv) (homPi: (ti1 ti2: TypeInfo Ty (Ty2::tys)) → hce.Ap₂ ti1 ti2) (ti1 ti2: TypeInfo Ty2 tys) : hce.Ap₂ ti1 ti2 :=
  (hce.compEquiv Ty Ty2 tys homPi).snd ti1 ti2

def consPi (hce: HomCompEquiv) (pi: ((ti: TypeInfo Ty []) → hce.Ap₂ ti ti)) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ ti1 ti2) (ti1 ti2: TypeInfo Ty (Ty2::tys)) : hce.Ap₂ ti1 ti2 :=
  (hce.compEquiv Ty Ty2 tys).symm ⟨pi, homPi⟩ ti1 ti2


def embedLeft (hce: HomCompEquiv) (pi: ((ti: TypeInfo Ty []) → hce.Ap₂ ti ti)) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ ti1 ti2) (ti1: TypeInfo Ty2 tys) (ti2: TypeInfo Ty (Ty2::tys)) : hce.Ap₂ (ti1.cons Ty) ti2 :=
  hce.consPi pi homPi (ti1.cons Ty) ti2

def embedRight (hce: HomCompEquiv) (pi: ((ti: TypeInfo Ty []) → hce.Ap₂ ti ti)) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ ti1 ti2) (ti1: TypeInfo Ty (Ty2::tys)) (ti2: TypeInfo Ty2 tys) : hce.Ap₂ ti1 (ti2.cons Ty) :=
  hce.consPi pi homPi ti1 (ti2.cons Ty)

def embed (hce: HomCompEquiv) (pi: ((ti: TypeInfo Ty []) → hce.Ap₂ ti ti)) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ ti1 ti2) (ti1 ti2: TypeInfo Ty2 tys) : hce.Ap₂ (ti1.cons Ty) (ti2.cons Ty) :=
  hce.consPi pi homPi (ti1.cons Ty) (ti2.cons Ty)

def consToFreeBiGeneric (hce: HomCompEquiv) (Ty: Type u) : FreeBiGeneric where
  specialize _ _ ti1 ti2 := hce.Ap₂ (ti1.cons Ty) (ti2.cons Ty)




--def consEmbedded (hce: HomCompEquiv) (pi: ((ti: TypeInfo Ty []) → hce.Ap₂ ti ti)) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ (ti1.cons Ty) (ti2.cons Ty)) (ti1 ti2: TypeInfo Ty (Ty2::tys)) : hce.Ap₂ ti1 ti2 :=


--def liftEmbedded (hce: HomCompEquiv) (Ty: Type u) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ (ti1.cons Ty) (ti2.cons Ty)) (ti1 ti2: TypeInfo Ty2 tys) : hce.Ap₂ ti1 ti2 :=


end HomCompEquiv



end FreeBiGeneric



end TypeTable




end Nemonuri.TypeLists.IterSum

end
