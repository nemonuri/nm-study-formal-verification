module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Nemonuri

class FinsetLike (A: Type _) (B: outParam <| Type _) where
  protected coe : A → Finset B
  coe_injective : Function.Injective coe

attribute [coe] FinsetLike.coe

namespace FinsetLike

variable {A: Type _} {B: Type _} [FinsetLike A B]

instance : CoeOut A (Finset B) where coe := FinsetLike.coe

instance : SetLike A B where
  coe a := FinsetLike.coe a
  coe_injective a1 a2 := by simp [FinsetLike.coe_injective.eq_iff]


instance {α: Type _} : FinsetLike (Finset α) α where
  coe := id
  coe_injective := Function.injective_id


def coeBoolPredFor {α: Type _} (fs: Finset α) (f: fs → Bool) : Finset fs :=
  fs.attach.filter (f · = .true)

theorem coeBoolPredFor_injective {α: Type _} (fs: Finset α) : Function.Injective (coeBoolPredFor fs) := by
  intro f1 f2
  simp only [coeBoolPredFor]
  intro lm1
  simp [SetLike.ext_iff] at lm1
  ext x
  specialize lm1 x.val x.property
  simpa using lm1


instance {α: Type _} (fs: Finset α) : FinsetLike (fs → Bool) fs where
  coe := coeBoolPredFor fs
  coe_injective := coeBoolPredFor_injective fs

instance {α: Type _} [Fintype α] : FinsetLike (Fintype α) α where
  coe _ := Finset.univ
  coe_injective ft1 ft2 _ := Fintype.subsingleton α |>.allEq ft1 ft2


theorem fintype_coe_eq_univ {α: Type _} [ft: Fintype α] : (ft: Finset α) = Finset.univ := rfl


end FinsetLike

end Nemonuri

end
