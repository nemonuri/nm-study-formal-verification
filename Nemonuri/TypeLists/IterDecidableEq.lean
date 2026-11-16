module


public import Mathlib.Logic.IsEmpty.Defs


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists


inductive IterDecidableEq.{u} : List (Type u) → Type _ where
  | nil : IterDecidableEq []
  | cons (Head: Type u) (tail: List (Type u)) (deq: DecidableEq Head) (iter: IterDecidableEq tail) : IterDecidableEq (Head :: tail)

namespace IterDecidableEq

universe u

def decidableEqOfHead {Ty: Type u} {tys: List (Type u)} (iter: IterDecidableEq (Ty :: tys)) : DecidableEq Ty :=
  match iter with
  | .cons _ _ deq _ => deq

noncomputable def ofClassical (tys: List (Type u)) : IterDecidableEq tys :=
  match tys with
  | [] => .nil
  | Ty::tys => .cons Ty tys (Classical.typeDecidableEq Ty) (ofClassical tys)

theorem eq_ofClassical (tys: List (Type u)) (iter: IterDecidableEq tys) : iter = ofClassical tys := by
  rcases iter with _ | ⟨Ty, tys, deq, iter⟩
  · dsimp [ofClassical]
  · dsimp [ofClassical]
    congr
    · exact Subsingleton.elim _ _
    · exact eq_ofClassical tys iter

protected instance subsingleton (tys: List (Type u)) : Subsingleton (IterDecidableEq tys) where
  allEq := by
    intro a b
    rw [eq_ofClassical tys a, eq_ofClassical tys b]


end IterDecidableEq


class HasIterDecidableEq.{u} (tys: List (Type u)) where
  iterDecidableEq: IterDecidableEq tys



end Nemonuri.TypeLists

end
