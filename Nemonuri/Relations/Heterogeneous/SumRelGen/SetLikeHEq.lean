module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.IsSubIntersection

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} --{rel: αl → αr → Prop}

namespace SumUnion

def SetLikeHEq (rel: αl → αr → Prop) (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] (sal: Sαl) (sar: Sαr) : Prop := SetHEq rel sal sar

variable {rel: αl → αr → Prop} {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr}

@[defeq]
theorem setLikeHEq_def : SetLikeHEq rel Sαl Sαr sal sar = SetHEq rel ↑sal ↑sar := rfl

namespace SetLikeHEq

theorem of_setHEq (rel: αl → αr → Prop) (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr} (req: SetHEq rel ↑sal ↑sar) : SetLikeHEq rel Sαl Sαr sal sar := req

theorem leftUnique_of (rel: αl → αr → Prop) [IsBiUnique rel] (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : Relator.LeftUnique (SetLikeHEq rel Sαl Sαr) := by
  intro sl1 sl2 sr lm1 lm2
  dsimp [setLikeHEq_def] at lm1 lm2
  have lm3 := SetHEq.leftUnique_of_rel rel lm1 lm2
  simpa using lm3

theorem rightUnique_of (rel: αl → αr → Prop) [IsBiUnique rel] (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : Relator.RightUnique (SetLikeHEq rel Sαl Sαr) := by
  intro sl sr1 sr2 lm1 lm2
  dsimp [setLikeHEq_def] at lm1 lm2
  have lm3 := SetHEq.rightUnique_of_rel rel lm1 lm2
  simpa using lm3


variable [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr]

theorem projectLeftSetToRightSet_eq {sal: Sαl} {sar: Sαr} (h: SetLikeHEq rel Sαl Sαr ↑sal ↑sar) : projectLeftSetToRightSet rel ↑sal = ↑sar := by
  dsimp [setLikeHEq_def] at h
  exact h.projectLeftSetToRightSet_eq

theorem projectRightSetToLeftSet_eq {sal: Sαl} {sar: Sαr} (h: SetLikeHEq rel Sαl Sαr ↑sal ↑sar) : projectRightSetToLeftSet rel ↑sar = ↑sal := by
  dsimp [setLikeHEq_def] at h
  exact h.projectRightSetToLeftSet_eq


end SetLikeHEq

theorem setLikeHEq_iff_eq_and_eq [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr}
  : (SetLikeHEq rel Sαl Sαr ↑sal ↑sar) ↔ (projectLeftSetToRightSet rel ↑sal = ↑sar ∧ projectRightSetToLeftSet rel ↑sar = ↑sal) := by
  simp only [setLikeHEq_def, setHEq_iff_eq_and_eq]

/-
theorem setLikeHEq_iff [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr}
  : (SetLikeHEq rel Sαl Sαr ↑sal ↑sar) := by
  dsimp [setLikeHEq_def, setHEq_def]
  simp [Set.ext_iff]
  intro su
  simp [setOfLeftSet, setOfRightSet]
-/

attribute [-simp] Subtype.forall Subtype.exists
theorem setLikeHEq_iff_finset_setHEq [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr]
  {sal: Sαl} [Fintype sal] {sar: Sαr} [Fintype sar]
  : (SetLikeHEq rel Sαl Sαr ↑sal ↑sar) ↔
    (SetHEq rel ((Finset.univ: Finset ↑sal).map ⟨Subtype.val, Subtype.val_injective⟩) ((Finset.univ: Finset ↑sar).map ⟨Subtype.val, Subtype.val_injective⟩)) := by
  rename Fintype ↑sal => ftL
  rename Fintype ↑sar => ftR
  rcases ftL with ⟨fsL, lm1⟩
  rcases ftR with ⟨fsR, lm2⟩
  dsimp [Finset.univ]
  simp
  dsimp [setLikeHEq_def]
  simp [setHEq_iff_forall_iff]
  refine forall_congr' ?_
  intro su
  classical
  induction fsL using Finset.induction with
  | empty =>
    induction fsR using Finset.induction with
    | empty =>
      simp [Subtype.forall] at ⊢ lm1 lm2
      simp [lm1, lm2]
    | insert r fsR lm3 lm4 =>
      have lm5 : ¬(∀x, x ∈ fsR) := by simp; exists r
      simp [lm5] at lm4; clear lm4 lm5
      simp at ⊢ lm2
      simp [Subtype.forall] at lm1
      simp [lm1]
      cases su using indInlInrOfSum with
      | inl l =>
        simp [sum_simp]
        constructor
        · intro lm4
          refine ⟨?_, ?_⟩
          · exact lm4 r.val r.property
          · intro r2 lm5
            exact lm4 r2.val r2.property
        · rintro ⟨lm4, lm5⟩ r2 lm6
          specialize lm2 ⟨r2, lm6⟩
          rcases lm2 with lm2 | lm2
          · rewrite [← lm2] at lm4
            exact lm4
          · exact lm5 ⟨r2, lm6⟩ lm2
      | inr r0 =>
        simp [sum_simp]
        constructor
        · intro lm4
          refine ⟨?_, ?_⟩
          · exact lm4 r.val r.property
          · intro r2 lm5
            exact lm4 r2.val r2.property
        · rintro ⟨lm4, lm5⟩ r2 lm6
          specialize lm2 ⟨r2, lm6⟩
          rcases lm2 with lm2 | lm2
          · rewrite [← lm2] at lm4
            exact lm4
          · exact lm5 ⟨r2, lm6⟩ lm2
  | insert l fsL lm3 lm4 =>
    have lm5 : ¬(∀x, x ∈ fsL) := by simp; exists l
    simp [lm5] at lm4; clear lm4 lm5
    induction fsR using Finset.induction with
    | empty =>
      simp at ⊢ lm1
      simp [Subtype.forall] at lm2
      simp [lm2]
      cases su using indInlInrOfSum <;> (
        simp [sum_simp]
        constructor
        · intro lm4
          refine ⟨?_, ?_⟩
          · exact lm4 l.val l.property
          · intro l2 lm5
            exact lm4 l2.val l2.property
        · rintro ⟨lm4, lm5⟩ l2 lm6
          specialize lm1 ⟨l2, lm6⟩
          rcases lm1 with lm1 | lm1
          · rewrite [← lm1] at lm4
            exact lm4
          · exact lm5 ⟨l2, lm6⟩ lm1 )
    | insert r fsR lm5 lm6 =>
      have lm7 : ¬(∀x, x ∈ fsR) := by simp; exists r
      simp [lm7] at lm6; clear lm6 lm7
      simp at lm1 lm2 ⊢
      cases su using indInlInrOfSum with
      | inl l0 =>
        simp [sum_simp]
        constructor
        · intro lm6
          constructor
          · intro lm7
            rcases lm7 with lm7 | lm7
            · subst lm7
              simp at lm6
              rcases lm6 with ⟨r2, lm7, lm8⟩
              specialize lm2 ⟨r2, lm7⟩
              rcases lm2 with lm2 | lm2
              · rewrite [Eq.comm] at lm2
                subst lm2
                dsimp
                left
                exact lm8
              · right
                exists ⟨r2, lm7⟩
            · rcases lm7 with ⟨l2, lm8, lm9⟩
              subst lm9
              simp at lm6
              rcases lm6 with ⟨r2, lm9, lm10⟩
              specialize lm2 ⟨r2, lm9⟩
              rcases lm2 with lm2 | lm2
              · rewrite [Eq.comm] at lm2
                subst lm2
                dsimp
                left
                exact lm10
              · right
                exists ⟨r2, lm9⟩
          · intro lm7
            rcases lm7 with lm7 | lm7
            · replace lm6 := lm6.mpr ?h1
              case h1 => exists r.val; simp; exact lm7
              specialize lm1 ⟨l0, lm6⟩
              rcases lm1 with lm1 | lm1
              · rewrite [Eq.comm] at lm1
                subst lm1
                left
                dsimp
              · right
                exists ⟨l0, lm6⟩
            · rcases lm7 with ⟨r2, lm8, lm9⟩
              replace lm6 := lm6.mpr ?h1
              case h1 => exists r2.val; simp; exact lm9
              specialize lm1 ⟨l0, lm6⟩
              rcases lm1 with lm1 | lm1
              · rewrite [Eq.comm] at lm1
                subst lm1
                left
                dsimp
              · right
                exists ⟨l0, lm6⟩
        · intro lm6
          constructor
          · intro lm7
            specialize lm1 ⟨l0, lm7⟩
            rcases lm1 with lm1 | lm1
            · rewrite [Eq.comm] at lm1
              subst lm1
              simp at lm6
              rcases lm6 with lm6 | lm6
              · exists r.val; simp; exact lm6
              · rcases lm6 with ⟨r2, lm8, lm9⟩
                exists r2.val; simp; exact lm9
            · replace lm6 := lm6.mp ?h1
              case h1 => right; exists ⟨l0, lm7⟩
              rcases lm6 with lm6 | lm6
              · exists r; simp; exact lm6
              · rcases lm6 with ⟨r2, lm8, lm9⟩
                exists r2.val; simp; exact lm9
          · rintro ⟨r2, lm7, lm8⟩
            specialize lm2 ⟨r2, lm7⟩
            rcases lm2 with lm2 | lm2
            · rewrite [Eq.comm] at lm2
              subst lm2
              simp [lm8] at lm6
              rcases lm6 with lm6 | lm6
              · subst lm6; simp
              · rcases lm6 with ⟨l2, lm6, lm9⟩
                subst lm9; simp
            · replace lm6 := lm6.mpr ?h1
              case h1 => right; exists ⟨r2, lm7⟩
              rcases lm6 with lm6 | lm6
              · subst lm6; simp
              · rcases lm6 with ⟨l2, lm6, lm9⟩
                subst lm9; simp
        | inr r0 =>
          simp [sum_simp]
          constructor
          · intro lm6
            rewrite [Iff.comm] at ⊢ lm6
            constructor
            · intro lm7
              rcases lm7 with lm7 | lm7
              · subst lm7
                simp at lm6
                rcases lm6 with ⟨l2, lm7, lm8⟩
                specialize lm1 ⟨l2, lm7⟩
                rcases lm1 with lm1 | lm1
                · rewrite [Eq.comm] at lm1
                  subst lm1
                  dsimp
                  left
                  exact lm8
                · right
                  exists ⟨l2, lm7⟩
              · rcases lm7 with ⟨r2, lm8, lm9⟩
                subst lm9
                simp at lm6
                rcases lm6 with ⟨l2, lm9, lm10⟩
                specialize lm1 ⟨l2, lm9⟩
                rcases lm1 with lm1 | lm1
                · rewrite [Eq.comm] at lm1
                  subst lm1
                  dsimp
                  left
                  exact lm10
                · right
                  exists ⟨l2, lm9⟩
            · intro lm7
              rcases lm7 with lm7 | lm7
              · replace lm6 := lm6.mpr ?h1
                case h1 => exists l.val; simp; exact lm7
                specialize lm2 ⟨r0, lm6⟩
                rcases lm2 with lm2 | lm2
                · rewrite [Eq.comm] at lm2
                  subst lm2
                  left
                  dsimp
                · right
                  exists ⟨r0, lm6⟩
              · rcases lm7 with ⟨l2, lm8, lm9⟩
                replace lm6 := lm6.mpr ?h1
                case h1 => exists l2.val; simp; exact lm9
                specialize lm2 ⟨r0, lm6⟩
                rcases lm2 with lm2 | lm2
                · rewrite [Eq.comm] at lm2
                  subst lm2
                  left
                  dsimp
                · right
                  exists ⟨r0, lm6⟩
          · intro lm6
            rewrite [Iff.comm] at ⊢ lm6
            constructor
            · intro lm7
              specialize lm2 ⟨r0, lm7⟩
              rcases lm2 with lm2 | lm2
              · rewrite [Eq.comm] at lm2
                subst lm2
                simp at lm6
                rcases lm6 with lm6 | lm6
                · exists l.val; simp; exact lm6
                · rcases lm6 with ⟨r2, lm8, lm9⟩
                  exists r2.val; simp; exact lm9
              · replace lm6 := lm6.mp ?h1
                case h1 => right; exists ⟨r0, lm7⟩
                rcases lm6 with lm6 | lm6
                · exists l; simp; exact lm6
                · rcases lm6 with ⟨l2, lm8, lm9⟩
                  exists l2.val; simp; exact lm9
            · rintro ⟨l2, lm7, lm8⟩
              specialize lm1 ⟨l2, lm7⟩
              rcases lm1 with lm1 | lm1
              · rewrite [Eq.comm] at lm1
                subst lm1
                simp [lm8] at lm6
                rcases lm6 with lm6 | lm6
                · subst lm6; simp
                · rcases lm6 with ⟨r2, lm6, lm9⟩
                  subst lm9; simp
              · replace lm6 := lm6.mpr ?h1
                case h1 => right; exists ⟨l2, lm7⟩
                rcases lm6 with lm6 | lm6
                · subst lm6; simp
                · rcases lm6 with ⟨r2, lm6, lm9⟩
                  subst lm9; simp




      --| inr r0 =>
      --  simp [sum_simp]





/-
      cases su using indInlInrOfSum with
      | inl l =>
        simp [sum_simp] at ⊢ lm4
        by_cases lm5: ∃r2, r2 ∈ fsR
        · rcases lm5 with
-/
/-
  refine forall_congr' ?_
  intro su
  cases su using indInlInrOfSum with
  | inl l =>
    simp [sum_simp]
-/

end SumUnion



end Nemonuri.Relations.Heterogeneous

end
