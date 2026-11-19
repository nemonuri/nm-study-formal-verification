module

public import Nemonuri.TransitionSystem.Basic


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

universe u1 u2 u3


def IsActEq (tr: TransitionSystem.{u1, u2, u3}) (Act: Type u2) : Prop := tr.Act = Act

def IsApEq (tr: TransitionSystem.{u1, u2, u3}) (AP: Type u3) : Prop := tr.AP = AP

structure IsActApEq (tr: TransitionSystem.{u1, u2, u3}) (Act: Type u2) (AP: Type u3) where
  actEq: tr.IsActEq Act
  apEq: tr.IsApEq AP

variable {tr: TransitionSystem.{u1, u2, u3}}

theorem IsActEq.to_eq {Act: Type u2} (h: tr.IsActEq Act) : tr.Act = Act := h

theorem IsApEq.to_eq {AP: Type u3} (h: tr.IsApEq AP) : tr.AP = AP := h



inductive IterActAPType.{u4} (Pi: (TransitionSystem.{u1, u2, u3}) → (Type u2) → (Type u3) → List (TransitionSystem.{u1, u2, u3}) → List (Type u2) → List (Type u3) → Sort u4)
  : List (TransitionSystem.{u1, u2, u3}) → List (Type u2) → List (Type u3) → Sort _ where
  | nil : IterActAPType Pi [] [] []
  | cons (tr: TransitionSystem.{u1, u2, u3}) (ActTy: Type u2) (ApTy: Type u3) --(sigma: Pi tr ActTy ApTy)
         (trs: List (TransitionSystem.{u1, u2, u3})) (actTys: List (Type u2)) (apTys: List (Type u3))
         (sigma: Pi tr ActTy ApTy trs actTys apTys)
         : IterActAPType Pi trs actTys apTys → IterActAPType Pi (tr::trs) (ActTy::actTys) (ApTy::apTys)




end Nemonuri.TransitionSystem

end
