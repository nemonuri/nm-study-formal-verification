module


public import Nemonuri.TypeLists.IterSum.Explicit

@[expose] public section

set_option autoImplicit false


namespace Nemonuri.TypeLists.IterSum


universe u u2 u3


namespace TypeInfo

structure FreeGeneric where
  specialize (Ty: Type u) (tys: List (Type u)) : TypeInfo Ty tys → Sort u2

namespace FreeGeneric

def Ap (lg: FreeGeneric) ⦃Ty: Type u⦄ ⦃tys: List (Type u)⦄ (ti: TypeInfo Ty tys) : Sort u2 := lg.specialize Ty tys ti

end FreeGeneric

structure FreeGenericHom (lg1: FreeGeneric.{u, u2}) (lg2: FreeGeneric.{u, u3}) where
  specialize (Ty: Type u) (tys: List (Type u)) (ti1 ti2: TypeInfo Ty tys) : (lg1.Ap ti1) → (lg2.Ap ti2)


namespace FreeGenericHom

variable {lg1: FreeGeneric.{u, u2}} {lg2: FreeGeneric.{u, u3}}

def Ap₂ (lgh: FreeGenericHom lg1 lg2) ⦃Ty: Type u⦄ ⦃tys: List (Type u)⦄ (ti1 ti2: TypeInfo Ty tys) : (lg1.Ap ti1) → (lg2.Ap ti2) :=
  lgh.specialize Ty tys ti1 ti2

end FreeGenericHom


structure FreeBiGeneric where
  specialize (Ty: Type u) (tys: List (Type u)) : TypeInfo Ty tys → TypeInfo Ty tys → Sort u2

namespace FreeBiGeneric

def Ap₂ (lgh: FreeBiGeneric) ⦃Ty: Type u⦄ ⦃tys: List (Type u)⦄ (ti1 ti2: TypeInfo Ty tys) : Sort u2 := lgh.specialize _ _ ti1 ti2


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


namespace HomCompEquiv

variable {Ty Ty2: Type u} {tys: List (Type u)}

def head (hce: HomCompEquiv) (homPi: (ti1 ti2: TypeInfo Ty (Ty2::tys)) → hce.Ap₂ ti1 ti2) (ti: TypeInfo Ty []) : hce.Ap₂ ti ti :=
  (hce.compEquiv Ty Ty2 tys homPi).fst ti

def tail (hce: HomCompEquiv) (homPi: (ti1 ti2: TypeInfo Ty (Ty2::tys)) → hce.Ap₂ ti1 ti2) (ti1 ti2: TypeInfo Ty2 tys) : hce.Ap₂ ti1 ti2 :=
  (hce.compEquiv Ty Ty2 tys homPi).snd ti1 ti2

def cons (hce: HomCompEquiv) (homPi: (ti1 ti2: TypeInfo Ty2 tys) → hce.Ap₂ ti1 ti2) {ti: TypeInfo Ty []} (hom: hce.Ap₂ ti ti) (ti1 ti2: TypeInfo Ty (Ty2::tys)) : hce.Ap₂ ti1 ti2 :=
  let fst (ti0: TypeInfo Ty []) : hce.Ap₂ ti0 ti0 := hom |> cast (by congr <;> exact Subsingleton.elim _ _)
  (hce.compEquiv Ty Ty2 tys).symm ⟨fst, homPi⟩ ti1 ti2


end HomCompEquiv



end FreeBiGeneric



end TypeInfo




end Nemonuri.TypeLists.IterSum

end
