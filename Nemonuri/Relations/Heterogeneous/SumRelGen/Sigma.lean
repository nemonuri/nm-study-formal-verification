module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous.SumUnion

variable {αl αr: Type*} {βl: αl → Type*} {βr: αr → Type*}

def fstElim {rel2: Sigma βl → Sigma βr → Prop} [IsBiUnique rel2]
            (rel: αl → αr → Prop) (req: ∀sl sr, rel2 sl sr → rel sl.fst sr.fst)
            (su2: SumUnion rel2) : SumUnion rel :=
  let fstFun : (Sigma βl ⊕ Sigma βr) → αl ⊕ αr
    | .inl sl => .inl sl.fst
    | .inr sr => .inr sr.fst
  su2.liftOfSum (ofSum ∘ fstFun) (by
    intro s1 s2 lm1
    replace lm1 := lm1.eq_or_rel_exists IsBiUnique.biUnique
    rcases lm1 with lm1 | ⟨sl, sr, lm1, lm2⟩
    · subst lm1
      rfl
    · rcases lm2 with ⟨lm2, lm3⟩ | ⟨lm2, lm3⟩
      <;> (subst lm2 lm3 fstFun; simp [ofSum_eq_iff_sumEquivGen])
      · refine .rel _ _ ?_
        refine .intro _ _ ?_
        exact req _ _ lm1
      · refine .symm _ _ ?_
        refine .rel _ _ ?_
        refine .intro _ _ ?_
        exact req _ _ lm1 )



end Nemonuri.Relations.Heterogeneous.SumUnion

end
