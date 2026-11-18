module


public import Nemonuri.TypeLists.BiIter.IterRel

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists.BiIter.IterRel₂

universe u

def SumEquiv {tys: List (Type u)} (irel: IterRel₂ tys) : IterSum tys → IterSum tys → Prop := Relation.TransGen irel.SumRel

@[defeq]
theorem sumEquiv_def {tys: List (Type u)} (irel: IterRel₂ tys) : SumEquiv irel = Relation.TransGen irel.SumRel := rfl


namespace SumEquiv

variable {tys: List (Type u)} {irel: IterRel₂ tys}

variable (irel) in
@[refl]
protected theorem refl (isum: IterSum tys) : irel.SumEquiv isum isum := by
  dsimp [SumEquiv]
  refine .single ?_
  rfl

instance : Std.Refl irel.SumEquiv := ⟨SumEquiv.refl irel⟩

instance : Std.Symm irel.SumEquiv := (Relation.TransGen.stdSymm: Std.Symm (Relation.TransGen irel.SumRel))


protected theorem trans {isum1 isum2 isum3: IterSum tys} (h1: irel.SumEquiv isum1 isum2) (h2: irel.SumEquiv isum2 isum3) : irel.SumEquiv isum1 isum3 :=
  Relation.TransGen.trans h1 h2

variable (irel) in
protected theorem equivalence : Equivalence (irel.SumEquiv) where
  refl := Std.Refl.refl
  symm := Std.Symm.symm _ _
  trans lm1 lm2 := SumEquiv.trans lm1 lm2

instance : Trans irel.SumEquiv irel.SumEquiv irel.SumEquiv where
  trans := SumEquiv.trans



end SumEquiv

variable {tys: List (Type u)} {irel: IterRel₂ tys} in
theorem sumEquiv_iff (isum1 isum2: IterSum tys) : (irel.SumEquiv isum1 isum2) ↔ (irel.SumRel isum1 isum2) ∨ (∃isum3, irel.SumEquiv isum1 isum3 ∧ irel.SumRel isum3 isum2) := by
  dsimp [sumEquiv_def]
  exact Relation.transGen_iff irel.SumRel isum1 isum2


end Nemonuri.TypeLists.BiIter.IterRel₂

end
