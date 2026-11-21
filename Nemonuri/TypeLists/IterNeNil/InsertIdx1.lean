module


public import Nemonuri.TypeLists.IterNeNil.Basic

@[expose] public section

set_option autoImplicit false


namespace Nemonuri.TypeLists.IterNeNil


universe u u2


inductive InsertIdx1 (Pi: Type u → List (Type u) → Sort u2) : Type u → List (Type u) → Sort _ where
  | single (Ty: Type u) (sigma: Pi Ty []) : InsertIdx1 Pi Ty []
  | insert (Ty1 Ty2: Type u) (tys: List (Type u)) (sigma: Pi Ty1 (Ty2::tys)) : InsertIdx1 Pi Ty1 tys → InsertIdx1 Pi Ty1 (Ty2::tys)

--variable {Pi: Type u → List (Type u) → Sort u2} {Ty: Type u} {tys: List (Type u)} (tree: IterNeNil (InsertIdx1 Pi) Ty tys)

--(Ty: Type u) → (tys: List (Type u)) → (IterNeNil (InsertIdx1 Pi) Ty tys) → Prop

inductive ExtendsBi (Pi: Type u → Type u → Sort u2) : Type u → List (Type u) → Sort _ where
  | nil (Ty: Type u) : ExtendsBi Pi Ty []
  | cons (Ty1 Ty2: Type u) (tail: List (Type u)) (sigma: Pi Ty1 Ty2) : ExtendsBi Pi Ty1 (Ty2::tail)



end Nemonuri.TypeLists.IterNeNil

end
