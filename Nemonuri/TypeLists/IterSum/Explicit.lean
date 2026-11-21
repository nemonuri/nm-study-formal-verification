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



end Explicit


structure Box (Ty: Type u) (tys: List (Type u)) (i: Nat) where
  InnerType: Type u
  explicit: Explicit InnerType i Ty tys

/-- StateT 의 정의를 따라함. -/
@[implicit_reducible]
def BoxT.{u2, u3} (Ty: Type u) (tys: List (Type u)) (i: Nat) (m: Type u2 → Type u3) (boxToType: Box Ty tys i → Type u2) : Type (max (u+1) u3) :=
  (box: Box Ty tys i) → m (boxToType box)

@[reducible]
def BoxM.{u2} (Ty: Type u) (tys: List (Type u)) (i: Nat) (boxToType: Box Ty tys i → Type u2) : Type (max (u+1) u2) := BoxT Ty tys i Id boxToType

end Nemonuri.TypeLists.IterSum

end
