module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} {βl βr: Type*}

def setOfLeftElem (rel: αl → αr → Prop) : Set αl := { l | ∃r, rel l r }

def setOfRightElem (rel: αl → αr → Prop) : Set αr := { r | ∃l, rel l r }



def FunHEq (relA: αl → αr → Prop) (relB: βl → βr → Prop) (fl: αl → βl) (fr: αr → βr) : Prop :=
  ∀⦃l r⦄, SumEquivGen relA (.inl l) (.inr r) → SumEquivGen relB (.inl (fl l)) (.inr (fr r))

variable {relA: αl → αr → Prop} {relB: βl → βr → Prop} {fl: αl → βl} {fr: αr → βr}

theorem funHEq_def : FunHEq relA relB fl fr = (∀(l r), SumEquivGen relA (.inl l) (.inr r) → SumEquivGen relB (.inl (fl l)) (.inr (fr r))) := rfl

theorem funHEq_iff [IsBiUnique relA] [IsBiUnique relB] : FunHEq relA relB fl fr ↔ (∀(l r), relA l r → relB (fl l) (fr r)) := by
  dsimp [funHEq_def]
  simp [sumEquivGen_inl_inr_iff]


namespace SumUnion

variable (relA) in
def embedLeftFunD [IsBiUnique relA] [HasPartialCongruence relA] (dftAL: αl) (fl: αl → βl) (su: SumUnion relA) : βl := fl (su.leftD dftAL)

theorem embedLeftFunD_injective [IsBiUnique relA] [HasPartialCongruence relA] {dftAL: αl} : Function.Injective (embedLeftFunD relA dftAL: (αl → βl) → SumUnion relA → βl) := by
  intro fl1 fl2 lm1
  simp [funext_iff] at ⊢ lm1
  intro l
  specialize lm1 (.ofSum (.inl l))
  dsimp [embedLeftFunD, leftD, left?, funElim_eq_ofSum] at lm1
  exact lm1

variable (relA) in
def embedRightFunD [IsBiUnique relA] [HasPartialCongruence relA] (dftAR: αr) (fr: αr → βr) (su: SumUnion relA) : βr := fr (su.rightD dftAR)


def embedRightFunD_injective [IsBiUnique relA] [HasPartialCongruence relA] {dftAR: αr} : Function.Injective (embedRightFunD relA dftAR: (αr → βr) → SumUnion relA → βr) := by
  intro fr1 fr2 lm1
  simp [funext_iff] at ⊢ lm1
  intro r
  specialize lm1 (.ofSum (.inr r))
  dsimp [embedRightFunD, rightD, right?, funElim_eq_ofSum] at lm1
  exact lm1


variable (relB fl fr) in
def funElim₂ [IsBiUnique relA] (req: FunHEq relA relB fl fr) (su: SumUnion relA) : SumUnion relB :=
  su.funElim (fun l => (.ofSum (.inl (fl l)): SumUnion relB)) (fun r => (.ofSum (.inr (fr r)): SumUnion relB)) (by
    simp [funHEq_def, sumEquivGen_iff] at req
    simp [ofSum_eq_iff_sumEquivGen]
    exact req )



/-
variable (relA relB) in
def seqFunD [IsBiUnique relA] [HasPartialCongruence relA] [IsBiUnique relB] (dftAL: αl) (dftAR: αr) (fsu: SumUnion (FunHEq relA relB)) : SumUnion relA → SumUnion relB :=
  let sumFun : ((αl → βl) ⊕ (αr → βr)) → SumUnion relA → SumUnion relB
    | .inl fl => .ofSum ∘ .inl ∘ (embedLeftFunD relA dftAL fl)
    | .inr fr => .ofSum ∘ .inr ∘ (embedRightFunD relA dftAR fr)
  fsu.liftOfSum sumFun (by
    intro fs1 fs2 lm1
    rcases fs1 with ⟨fl1⟩ | ⟨fr1⟩
    <;> rcases fs2 with ⟨fl2⟩ | ⟨fr2⟩
    <;> (subst sumFun; dsimp)
    · refine funext ?_
      simp [inl_eq_inl_iff_eq]
      rw [← funext_iff, embedLeftFunD_injective.eq_iff]
      refine funext ?_
  )
-/

end SumUnion

structure FunInter (relA: αl → αr → Prop) (relB: βl → βr → Prop) where
  left : αl → βl
  right : αr → βr
  heq : FunHEq relA relB left right

namespace FunInter

def toFun [IsBiUnique relA] (fi: FunInter relA relB) : SumUnion relA → SumUnion relB := SumUnion.funElim₂ relB fi.left fi.right fi.heq

open SumUnion in
theorem toFun_injective [IsBiUnique relA] [IsBiUnique relB] : Function.Injective (toFun: FunInter relA relB → _) := by
  intro fi1 fi2 lm3
  rcases fi1 with ⟨fl1, fr1, lm1⟩
  rcases fi2 with ⟨fl2, fr2, lm2⟩
  simp [funext_iff] at ⊢ lm3
  simp [funHEq_def] at lm1 lm2
  dsimp [toFun] at lm3
  refine ⟨?_, ?_⟩
  · intro l
    specialize lm3 (.ofSum (.inl l))
    dsimp [funElim₂, funElim_eq_ofSum] at lm3
    simp [inl_eq_inl_iff_eq] at lm3
    exact lm3
  · intro r
    specialize lm3 (.ofSum (.inr r))
    dsimp [funElim₂, funElim_eq_ofSum] at lm3
    simp [inr_eq_inr_iff_eq] at lm3
    exact lm3

instance [IsBiUnique relA] [IsBiUnique relB] : FunLike (FunInter relA relB) (SumUnion relA) (SumUnion relB) where
  coe := toFun
  coe_injective := toFun_injective

end FunInter


namespace FunHEq

/-
theorem leftUnique [IsBiUnique relA] [IsBiUnique relB] : Relator.LeftUnique (FunHEq relA relB) := by
  intro fl1 fl2 fr lm1 lm2
  refine funext ?_
  intro l
  simp [funHEq_iff] at lm1 lm2
  specialize lm1 l
  specialize lm2 l
  by_cases lm3: ∃r, relA l r
  · rcases lm3 with ⟨r, lm3⟩
    specialize lm1 r lm3
    specialize lm2 r lm3
    exact IsBiUnique.leftUnique lm1 lm2
  · simp at lm3
    simp [lm3] at lm1 lm2; clear lm1 lm2
-/


end FunHEq

end Nemonuri.Relations.Heterogeneous

end
