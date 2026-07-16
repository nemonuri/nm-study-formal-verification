module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

--def Equiv.Finset.univ {α: Type _} [Fintype α] : α ≃ (.univ: Finset α) where
--  toFun


namespace Nemonuri

@[simps]
def finsetUnivEquiv {α: Type _} [Fintype α] : α ≃ (.univ: Finset α) where
  toFun x := ⟨x, Finset.mem_univ x⟩
  invFun x := x.val

--#print Nemonuri.finsetUnivEquiv_apply_coe

class FinsetLike (A: Type _) (B: outParam <| Type _) where
  protected coe : A → Finset B
  coe_injective : Function.Injective coe

attribute [coe] FinsetLike.coe

namespace FinsetLike

variable {A: Type _} {B: Type _} [FinsetLike A B]

instance : CoeHead A (Finset B) where coe := FinsetLike.coe

/-
instance : SetLike A B where
  coe a := FinsetLike.coe a
  coe_injective a1 a2 := by simp [FinsetLike.coe_injective.eq_iff]
-/

theorem finset_mem_iff_set_mem (A B: Type _) [FinsetLike A B] (a: A) (b: B)
  : b ∈ (a: Finset B) ↔ b ∈ (a: Set B) := by
  rfl
  --rfl


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

/-
instance {α: Type _} [Fintype α] : FinsetLike (Fintype α) α where
  coe _ := Finset.univ
  coe_injective ft1 ft2 _ := Fintype.subsingleton α |>.allEq ft1 ft2
-/

instance {α: Type _} [Fintype α] : FinsetLike (α → Bool) α where
  coe f := (.univ: Finset α).filter (f · = .true)
  coe_injective f1 f2 := by
    simp only
    intro lm1
    simp [SetLike.ext_iff] at lm1
    ext x
    exact lm1 x


instance coeToUniv {α: Type _} [Fintype α] : FinsetLike (Finset α) (.univ: Finset α) where
  coe fs := fs.map finsetUnivEquiv.toEmbedding
  coe_injective fs1 fs2 := by
    simp only [Finset.map_inj]
    exact id

theorem coeToUniv_mem_iff {α: Type _} [Fintype α] (fs: Finset α) (a: α)
  : (finsetUnivEquiv a) ∈ ((@coeToUniv α _).coe fs) ↔ a ∈ fs := by
  unfold coeToUniv
  simp only [Finset.mem_map_mk]

@[simp]
theorem coeToUniv_mem_iff' {α: Type _} [Fintype α] (fs: Finset α) (a: (.univ: Finset α))
  : a ∈ ((@coeToUniv α _).coe fs) ↔ (a.val) ∈ fs := by
  unfold coeToUniv
  simp only [Finset.mem_map_equiv, finsetUnivEquiv_symm_apply]


end FinsetLike

end Nemonuri

end
