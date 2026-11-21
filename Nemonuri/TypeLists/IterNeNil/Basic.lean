module


public import Nemonuri.TypeLists.IterSum

@[expose] public section

set_option autoImplicit false


namespace Nemonuri.TypeLists


inductive IterNeNil.{u, u2} (Pi: Type u → List (Type u) → Sort u2) : Type u → List (Type u) → Sort _ where
  | single (Ty: Type u) (sigma: Pi Ty []) : IterNeNil Pi Ty []
  | cons (Ty1 Ty2: Type u) (tys: List (Type u)) (sigma: Pi Ty1 (Ty2::tys)) : IterNeNil Pi Ty2 tys → IterNeNil Pi Ty1 (Ty2::tys)

universe u u2


namespace IterNeNil

variable {Pi: Type u → List (Type u) → Sort u2} {Ty: Type u} {Ty2: Type u} {tys: List (Type u)}


def length {Ty tys} : IterNeNil Pi Ty tys → Nat
  | .single _ _ => 0
  | .cons _ _ _ _ bi => bi.length + 1

@[defeq, simp]
theorem length_single {sigma} : (@IterNeNil.single Pi Ty sigma).length = 0 := rfl

@[defeq, simp]
theorem length_cons {inn: IterNeNil Pi Ty2 tys} {sigma} : (IterNeNil.cons Ty Ty2 tys sigma inn).length = inn.length + 1 := rfl



structure Generator {Pi: Type u → List (Type u) → Sort u2} (pi: (Ty: Type u) → (tys: List (Type u)) → Pi Ty tys) (Ty: Type u) (tys: List (Type u)) where





end IterNeNil



/-
inductive IterRel : Type u → List (Type u) → Sort _ where
  | nil (Ty: Type u) : IterRel Ty []
  | cons (Ty1 Ty2: Type u) (tail: List (Type u)) (v: Ty1 → Ty2 → Prop) : IterRel Ty1 tail → IterRel Ty1 (Ty2::tail)

def IterRel₂ (Ty: Type u) (tys: List (Type u)) : Type _ := IterNeNil (IterRel) Ty tys

#check List.insert
-/

/-
  | double (Ty1 Ty2: Type u) (v: Ty1 → Ty2 → Prop) : IterHRel Ty1 Ty2 []
  | cons (Ty1 Ty2 Ty3: Type u) (tail: List (Type u)) (v: Ty1 → Ty2 → Prop) :
-/

end Nemonuri.TypeLists
