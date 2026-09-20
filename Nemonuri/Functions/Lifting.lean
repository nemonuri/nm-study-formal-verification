module

public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Data.FunLike.Embedding


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions

structure Lifting (α β: Type*) where
  toFun: α → β
  surjective : Function.Surjective toFun


namespace Lifting

variable {α β: Type*}

instance : FunLike (Lifting α β) α β where
  coe x := x.toFun
  coe_injective := by rintro ⟨l1,_⟩ ⟨l2,_⟩; simp

theorem coe_surjective {l: Lifting α β} : Function.Surjective l := l.surjective

@[elab_as_elim]
theorem coind (l: Lifting α β)
  {motive: β → Prop}
  (intro: (x: α) → motive (l x))
  (t: β)
  : motive t := by
  have lm1 := l.coe_surjective
  dsimp [Function.Surjective] at lm1
  rcases lm1 t with ⟨x, lm2⟩
  rewrite [Eq.comm] at lm2
  subst lm2
  exact intro x


structure Inverse (l: Lifting α β) where
  toFun: β → α
  rightInverse: Function.RightInverse toFun l

theorem domain_nonempty [Nonempty β] {l: Lifting α β} : Nonempty α := Function.Surjective.nonempty l.coe_surjective

theorem domain_nontrivial [Nontrivial β] {l: Lifting α β} : Nontrivial α := Function.Surjective.nontrivial l.coe_surjective

--set_option trace.Meta.synthInstance true in
/-
theorem nonempty_of_codomain_nonempty [Nonempty β] : Nonempty (Lifting α β) := by
  have lm1 : Nonempty (α → β) := Pi.instNonempty
  rcases lm1 with ⟨fn1⟩
  have lm2: Function.Surjective fn1 := by
    dsimp [Function.Surjective]
    intro xb
-/
  --refine .intro ?_



/-
set_option trace.Meta.synthInstance true in
#synth Nonempty (α → β)
-/

--theorem nontrivial_of_codomain_nontrivial [Nontrivial β] : Nontrivial (Lifting α β) := by
  --rename_i lm1
  --simp [nontrivial_iff]
  --have lm1 := l.domain_nontrivial

namespace Inverse

variable {l: Lifting α β}

instance : FunLike (l.Inverse) β α where
  coe li := li.toFun
  coe_injective := by rintro ⟨_, li1⟩ ⟨_, li2⟩; simp

theorem coe_rightInverse {li: l.Inverse} : Function.RightInverse li l := li.rightInverse

theorem coe_leftInverse {li: l.Inverse} : Function.LeftInverse l li := li.coe_rightInverse

theorem coe_injective {li: l.Inverse} : Function.Injective li := li.coe_leftInverse.injective

instance : EmbeddingLike (l.Inverse) β α where
  injective' il := il.coe_injective

protected instance nonempty : Nonempty (l.Inverse) := by
  let finv := Function.surjInv l.coe_surjective
  refine .intro (.mk finv ?_)
  intro xb
  subst finv
  exact Function.surjInv_eq _ xb


/-
instance nontrivial_of_codomain_nontrivial [Nontrivial β] : Nontrivial (l.Inverse) := by
  have lm1 := l.domain_nontrivial
  have lm2 : Nonempty (l.Inverse) := inferInstance
  rcases lm2 with ⟨li⟩
  obtain ⟨a1, a2, lm2⟩ := lm1.exists_pair_ne
  simp [nontrivial_iff]
  by_contra lm3
  revert lm2
  simp at ⊢ lm3
  specialize lm3 li
  simp [DFunLike.ext_iff] at lm3
  have lm3_1 := fun il2 => lm3 il2 (l a1)
  have lm3_2 := fun il2 => lm3 il2 (l a2)
-/
  --rcases li with ⟨lif, lm4⟩
  --dsimp only [DFunLike.fun] at lm3

  --simp only [DFunLike. funext_iff] at lm3
  --simp at lm3
  --let b1 := l a1
  --let b2 := l a2
/-
  have lm3 := @li.coe_injective.eq_iff _ _ _ b1 b2
  subst b1 b2
  have lm4 := l.coe_surjective
  dsimp [Function.Surjective] at lm4
-/


end Inverse


end Lifting



end Nemonuri.Functions

end
