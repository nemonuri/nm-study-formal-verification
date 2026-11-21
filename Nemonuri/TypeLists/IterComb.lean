module


public import Nemonuri.TypeLists.IterSum

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists

universe u u2

inductive IterSub : List (Type u) → Type _ where
  | nil : IterSub []
  | cons (Head: Type u) (tail: List (Type u)) (isMem: Bool) : IterSub tail → IterSub (Head::tail)

namespace IterSub

def reduce {tys: List (Type u)} : IterSub tys → List (Type u)
  | .nil => []
  | .cons _ _ .false iter => reduce iter
  | .cons Ty _ .true iter => Ty::(reduce iter)


structure Combinator (Pi: List (Type u) → Sort u2) where
  nil : Pi []
  --cons (Ty: Type u)
  --nil : Pi .nil
  --cons {Ty: Type u} (v: Ty) {tys: List (Type u)} (iter: IterSub tys) : IterSub (Ty::tys)


end IterSub

/-
inductive CombPi (Pi: Type u → List (Type u) → Sort u2) : Type u → (tail: List (Type u)) → IterSub tail → Sort _ where
  | neg (Head: Type u) (tail: List (Type u))
-/

end Nemonuri.TypeLists

end
