module

public import Nemonuri.PropositionalLogics.Eval

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.PropositionalLogics

namespace Eval

structure IsSatRel (AP: Type*) (μ: Eval AP) (rel: Eval AP → Formula AP → Prop) : Prop where
  true : rel μ (.true)
  atom (a: AP) : rel μ (.atom a) ↔ (μ a = .true)
  neg (x: Formula AP) : rel μ (¬ₚx) ↔ (¬rel μ x)
  and (x y: Formula AP) : rel μ (x ∧ₚ y) ↔ (rel μ x ∧ rel μ y)


namespace IsSatRel

variable {AP: Type*}

theorem forall_formula_iff {μ: Eval AP} {rel1 rel2: Eval AP → Formula AP → Prop}
  (h1: IsSatRel AP μ rel1) (h2: IsSatRel AP μ rel2) (fml: Formula AP) : rel1 μ fml ↔ rel2 μ fml := by
  rcases fml with _ | ⟨ap⟩ | ⟨fml⟩ | ⟨fmlL, fmlR⟩
  · simp only [h1.true, h2.true]
  · rw [h1.atom, h2.atom]
  · rw [(h1.neg fml), (h2.neg fml)]
    refine not_iff_not.mpr ?_
    exact forall_formula_iff h1 h2 fml
  · rw [(h1.and fmlL fmlR), (h2.and fmlL fmlR)]
    have lm1 := forall_formula_iff h1 h2 fmlL
    have lm2 := forall_formula_iff h1 h2 fmlR
    rw [lm1, lm2]


end IsSatRel


structure SatRel (AP: Type*) where
  rel: Eval AP → Formula AP → Prop
  valid (μ: Eval AP) : IsSatRel AP μ rel


namespace SatRel

variable {AP: Type*}

instance : Subsingleton (SatRel AP) where
  allEq := by
    rintro ⟨rel1, lm1⟩ ⟨rel2, lm2⟩
    simp [funext_iff]
    rintro ⟨ind⟩ fml
    specialize lm1 ⟨ind⟩
    specialize lm2 ⟨ind⟩
    exact IsSatRel.forall_formula_iff lm1 lm2 fml

end SatRel

end Eval

end Nemonuri.PropositionalLogics
