module

public import Nemonuri.Relations.Heterogeneous.IsBiUnique.SetLike

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*}

namespace PartialCongruenceStruct

def leftListToRightFinset? [DecidableEq αr] (pcs: PartialCongruenceStruct αl αr) (ls: List αl) : Option (Finset αr) :=
  match ls with
  | [] => .some ∅
  | l::ls =>
  match pcs.right? l with
  | .none => .none
  | .some r =>
  match pcs.leftListToRightFinset? ls with
  | .none => .none
  | .some rs => .some (insert r rs)


def rightListToLeftFinset? [DecidableEq αl] (pcs: PartialCongruenceStruct αl αr) (rs: List αr) : Option (Finset αl) :=
  match rs with
  | [] => .some ∅
  | r::rs =>
  match pcs.left? r with
  | .none => .none
  | .some l =>
  match pcs.rightListToLeftFinset? rs with
  | .none => .none
  | .some ls => .some (insert l ls)


theorem leftListToRightFinset?_eq_empty_some_iff [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} {ls: List αl}
  : (pcs.leftListToRightFinset? ls = .some ∅) ↔ (ls = []) := by
  constructor
  · intro lm1
    unfold leftListToRightFinset? at lm1
    split at lm1
    · rfl
    · split at lm1 <;> simp at lm1 ⊢
      split at lm1 <;> simp at lm1
  · intro lm1
    subst lm1
    rfl


@[defeq]
theorem leftListToRightFinset?_nil [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} : pcs.leftListToRightFinset? [] = .some ∅ := rfl

theorem leftListToRightFinset?_cons_of_tail_eq_none [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} {l ls} (req: pcs.leftListToRightFinset? ls = .none)
  : pcs.leftListToRightFinset? (l :: ls) = .none := by
  dsimp [leftListToRightFinset?]
  generalize pcs.right? l = r?
  rcases r? with _ | ⟨r⟩
  · dsimp
  · simp [req]

theorem leftListToRightFinset?_cons_of_head_eq_none [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} {l ls} (req: pcs.right? l = .none)
  : pcs.leftListToRightFinset? (l :: ls) = .none := by
  simp [leftListToRightFinset?, req]

/-
theorem leftListToRightFinset?_cons_of_head_ne_none_and_tail_ne_none [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} {l ls} (req1: pcs.leftListToRightFinset? ls ≠ .none) (req2: pcs.right? l ≠ .none)
  : pcs.leftListToRightFinset? (l :: ls) = .some ()
-/

def leftMultisetToRightFinset? [DecidableEq αr] (pcs: PartialCongruenceStruct αl αr) (ls: Multiset αl) : Option (Finset αr) :=
  ls.liftOn pcs.leftListToRightFinset? (by
    intro ls rs lm1
    change List.Perm ls rs at lm1
    induction lm1 with
    | nil => rfl
    | cons l lm1 lm2 =>
      dsimp [leftListToRightFinset?]
      generalize pcs.right? l = r?
      rcases r? with _ | ⟨r⟩
      · dsimp
      · dsimp
        rw [lm2]
    | swap l1 l2 ls =>
      dsimp [leftListToRightFinset?]
      generalize pcs.right? l1 = r1?
      generalize pcs.right? l2 = r2?
      rcases r2? with _ | ⟨r2⟩
      <;> rcases r1? with _ | ⟨r1⟩
      <;> dsimp
      · generalize pcs.leftListToRightFinset? ls = rs?
        rcases rs? with _ | ⟨rs⟩
        · dsimp
        · simp
          exact Finset.insert_comm _ _ _
    | trans lm1 lm2 lm3 lm4 =>
      exact lm3.trans lm4 )

def rightMultisetToLeftFinset? [DecidableEq αl] (pcs: PartialCongruenceStruct αl αr) (rs: Multiset αr) : Option (Finset αl) :=
  rs.liftOn pcs.rightListToLeftFinset? (by
    intro ls rs lm1
    change List.Perm ls rs at lm1
    induction lm1 with
    | nil => rfl
    | cons r lm1 lm2 =>
      dsimp [rightListToLeftFinset?]
      generalize pcs.left? r = l?
      rcases l? with _ | ⟨l⟩
      · dsimp
      · dsimp
        rw [lm2]
    | swap r1 r2 rs =>
      dsimp [rightListToLeftFinset?]
      generalize pcs.left? r1 = l1?
      generalize pcs.left? r2 = l2?
      rcases l2? with _ | ⟨l2⟩
      <;> rcases l1? with _ | ⟨l1⟩
      <;> dsimp
      · generalize pcs.rightListToLeftFinset? rs = ls?
        rcases ls? with _ | ⟨ls⟩
        · dsimp
        · simp
          exact Finset.insert_comm _ _ _
    | trans lm1 lm2 lm3 lm4 =>
      exact lm3.trans lm4 )


--theorem leftMultisetToRightFinset?_empty [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} : pcs.leftMultisetToRightFinset? ∅ =


def leftFinsetToRightFinset? [DecidableEq αr] (pcs: PartialCongruenceStruct αl αr) (ls: Finset αl) : Option (Finset αr) := pcs.leftMultisetToRightFinset? ls.val

def rightFinsetToLeftFinset? [DecidableEq αl] (pcs: PartialCongruenceStruct αl αr) (rs: Finset αr) : Option (Finset αl) := pcs.rightMultisetToLeftFinset? rs.val


theorem leftFinsetToRightFinset?_empty [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} : pcs.leftFinsetToRightFinset? ∅ = .some ∅ := rfl

@[defeq]
theorem leftFinsetToRightFinset?_eq_leftListToRightFinset?_of_nodup [DecidableEq αr] {pcs: PartialCongruenceStruct αl αr} {ls: List αl} (req: ls.Nodup)
  : pcs.leftFinsetToRightFinset? (⟨↑ls, req⟩) = pcs.leftListToRightFinset? ls :=
  rfl


end PartialCongruenceStruct


namespace IsPartialCongruence

variable {pcs: PartialCongruenceStruct αl αr} {rel: αl → αr → Prop}

open SumUnion
open PartialCongruenceStruct



/-
  generalize lm1: Finset.cons l ls req = ls2
  rcases ls2 with ⟨ls2, lm2⟩
  dsimp [leftFinsetToRightFinset?]
  cases ls2 using Quotient.ind
  rename_i ls2
  dsimp only [leftMultisetToRightFinset?, Quotient.liftOn_mk]
  rcases ls2 with _ | ⟨l2, ls2⟩
  · simp at lm1
  · simp at lm1
-/
    --dsimp [leftListToRightFinset?]
    --rcases Option.eq_none_or_eq_some


theorem leftListToRightFinset?_eq_none_iff [IsBiUnique rel] [DecidableEq αr] (h: IsPartialCongruence pcs rel) {ls: List αl}
  : (pcs.leftListToRightFinset? ls = .none) ↔ (∃l ∈ ls, ∀r, ¬rel l r) := by
  induction ls with
  | nil => simp [leftListToRightFinset?]
  | cons l ls lm2 =>
    dsimp [leftListToRightFinset?]
    generalize lm4: pcs.right? l = r?
    rcases r? with _ | ⟨r⟩
    · simp
      left
      exact h.right?_eq_none_iff_forall_not_rel.mp lm4
    · replace lm4 := h.rel_of_right?_eq_some lm4
      simp
      generalize lm5: pcs.leftListToRightFinset? ls = rs?
      rcases rs? with _ | ⟨rs⟩
      · simp
        right
        exact lm2.mp lm5
      · simp [lm5] at lm2
        simp
        refine ⟨?_, ?_⟩
        · exists r
        · exact lm2

theorem leftFinsetToRightFinset?_eq_none_iff [IsBiUnique rel] [DecidableEq αr] (h: IsPartialCongruence pcs rel) {ls: Finset αl}
  : (pcs.leftFinsetToRightFinset? ls = .none) ↔ (∃l ∈ ls, ∀r, ¬rel l r) := by
  rcases ls with ⟨ls, lm1⟩
  cases ls using Quotient.ind
  rename_i ls
  dsimp only [leftFinsetToRightFinset?, leftMultisetToRightFinset?, Quotient.liftOn_mk]
  simp
  exact h.leftListToRightFinset?_eq_none_iff

/-
theorem leftFinsetToRightFinset?_eq_some_iff_setlikeHEq_at [IsBiUnique rel] [DecidableEq αr] (h: IsPartialCongruence pcs rel) (ls: Finset αl) (rs: Finset αr)
  : (pcs.leftFinsetToRightFinset? ls = .some rs) ↔ (SetLikeHEq rel (Finset αl) (Finset αr) ls rs) := by
  simp [setLikeHEq_def, setHEq_iff_forall_iff_and_forall_iff]
  rcases ls with ⟨ls, lm1⟩
  --rcases rs with ⟨rs, lm2⟩
  dsimp [leftFinsetToRightFinset?, leftMultisetToRightFinset?]
  cases ls using Quotient.ind
  --cases rs using Quotient.ind
  rename_i ls --rs
  dsimp only [Quotient.liftOn_mk]
  simp
  cases ls with
  | nil =>
    dsimp [leftListToRightFinset?]
    simp [Finset.ext_iff]
    intro lm2 l r lm3
    specialize lm2 r
    contradiction
  | cons l ls => --lm2
    simp at lm1
    rcases lm1 with ⟨lm1, lm3⟩
    --simp at lm2 ⊢
    --specialize lm2 lm3
    cases rs using Finset.induction with
    | empty =>
      simp [leftListToRightFinset?_eq_empty_some_iff] --at ⊢ lm2
      intro lm4
      specialize lm4 l
      simp at lm4
    | insert r rs lm4 lm5 =>
      clear lm5
      simp
      dsimp [leftListToRightFinset?]
      generalize lm6: pcs.right? l = r?
      rcases r? with _ | ⟨r2⟩
      · simp
        intro lm7
        replace lm6 := h.right?_eq_none_iff_forall_not_rel.mp lm6
        specialize lm7 l
        simp at lm7
        simp [lm6] at lm7
      · replace lm6 := h.rel_of_right?_eq_some lm6
        simp
        generalize lm7: pcs.leftListToRightFinset? ls = rs?
        rcases rs? with _ | ⟨rs2⟩
        · simp
          --simp [lm7] at lm2
          intro lm8
          have lm9 := h.leftListToRightFinset?_eq_none_iff.mp lm7
          rcases lm9 with ⟨l2, lm9, lm10⟩
          --have lm11 := lm8 l
          --simp at lm11
          have lm12 := lm8 l2
          simp [lm9] at lm12
          rcases lm12 with lm12 | lm12
          · specialize lm10 r
            contradiction
          · rcases lm12 with ⟨r3, lm12, lm13⟩
            specialize lm10 r3
            contradiction
        · simp [Finset.ext_iff]
          have lm8 := h.leftFinsetToRightFinset?_eq_some_iff_setlikeHEq_at ⟨↑ls, lm3⟩ rs2
          rewrite [pcs.leftFinsetToRightFinset?_eq_leftListToRightFinset?_of_nodup lm3] at lm8
          simp [lm7] at lm8
          simp [setLikeHEq_def, setHEq_iff_forall_iff_and_forall_iff] at lm8
          rcases lm8 with ⟨lm8, lm9⟩
          simp [lm9] at lm8 ⊢
          clear lm9
          constructor
          · intro lm9
            refine ⟨?_, ?_⟩
            · intro l2
              by_cases lm10: l = l2
              · subst lm10
                simp
                specialize lm9 r2
                simp at lm9
                by_cases lm10: r = r2
                · subst lm10
                  left
                  exact lm6
                · rewrite [Eq.comm] at lm10
                  simp [lm10] at lm9
                  right
                  exists r2
              · rewrite [Eq.comm] at lm10
                simp [lm10]
                have lm11 := lm8 l2
                simp [lm11]; clear lm11
                constructor
                · rintro ⟨r3, lm11, lm12⟩
                  rcases lm11 with ⟨l3, lm11, lm13⟩
                  have lm14 := IsBiUnique.leftUnique lm12 lm13
                  subst lm14; clear lm13
                  have lm14 := IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm6 lm12
                  rewrite [Eq.comm] at lm10
                  simp [lm10] at lm14
                  have lm15 := lm9 r3
                  rewrite [Eq.comm] at lm14
                  by_cases lm16: r = r3
                  · subst lm16
                    left
                    exact lm12
                  · rewrite [Eq.comm] at lm16
                    simp [lm16, lm14] at lm15
                    replace lm15 := lm15.mp ?h1
                    case h1 => exists l2
                    right
                    exists r3
                · intro lm11
                  by_cases lm12: rel l2 r
                  · clear lm11
                    have lm11 := IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm6 lm12
                    rewrite [Eq.comm] at lm10
                    simp [lm10] at lm11
                    rewrite [Eq.comm] at lm11
                    specialize lm9 r
                    simp [lm11] at lm9
                    exists r
                  · simp [lm12] at lm11
                    rcases lm11 with ⟨r3, lm11, lm13⟩
                    exists r3
                    refine ⟨?_, lm13⟩
                    exists l2
                    refine ⟨?_, lm13⟩
                    have lm14 := IsBiUnique.left_eq_iff_right_eq_of_rel₂ lm6 lm13
                    rewrite [Eq.comm] at lm10
                    simp [lm10] at lm14
                    specialize lm9 r3
                    rewrite [Eq.comm] at lm14
                    simp [lm11, lm14] at lm9
                    rcases lm9 with ⟨l3, lm15, lm16⟩
                    have lm17 := IsBiUnique.leftUnique lm13 lm16
                    subst lm17
                    exact lm15
            ·
-/
/-
                by_cases lm11: r = r2
                · subst lm11
                  specialize lm8 l2
                  simp [lm8]
                  constructor
                  · rintro ⟨r2, lm11, lm12⟩
                    rcases lm11 with ⟨l3, lm11, lm13⟩
                    have lm14 := IsBiUnique.leftUnique lm12 lm13
                    subst lm14; clear lm13
-/
                    --simp [lm11] at lm8
                    --rcases lm8 with ⟨r3, lm8, lm15⟩


/-
          constructor
          · intro lm10
            refine ⟨?_, ?_⟩
            · intro l2
              constructor
              · intro lm11
                rcases lm11 with lm11 | lm11
                · subst lm11
                  specialize lm8 l2
                  simp [lm1] at lm8
                  have lm11 := lm10 r
                  simp at lm11
                  by_cases lm12: r = r2
                  · subst lm12
                    left
                    exact lm6
                  · simp [lm12] at lm11
                    specialize lm8 r lm11
                    simp [lm8]
                    have lm13 := lm10 r2
                    rewrite [Eq.comm] at lm12
                    simp [lm12] at lm13
                    exists r2
                · by_cases lm12: l = l2
                  · subst lm12
                    contradiction
                  · by_cases lm13: r = r2
                    · subst lm13
                      specialize lm9 r
                      specialize lm8 l
                      simp [lm1] at lm8
                      by_cases lm14: r ∈ rs2
                      · specialize lm8 r lm14
                        contradiction
                      · simp [lm14] at lm9
                        have lm15 := lm9 l2 lm11
                        simp [lm15]
                        by_contra lm16
                        simp at lm16
                        revert lm9
                        simp
-/
/-
                    have lm13 := lm8 l
                    simp [lm1] at lm13
                    have lm14 := lm13 r2
                    simp [lm6] at lm14
                    have lm15 := lm9 r2
                    simp [lm14] at lm15
                    by_cases lm18: r = r2
                    · subst lm18
                      specialize lm15 l2 lm11
                      simp [lm15]
-/
/-

                    simp at lm13
                    by_cases lm14: r = r2
                    · subst lm14
-/
/-
                  rcases lm11 with lm11 | lm11
                  · subst lm11
                    left
                    exact lm6
                  · specialize lm8 r lm11
                    simp [lm8]
-/
/-
                  specialize lm8 l2

                  specialize lm8 r2
                  specialize lm9 r2
                  simp [lm9] at lm8
-/

/-
          simp [lm7, Finset.ext_iff] at lm2
          constructor
          · intro lm8
            specialize lm8 r
            simp at lm8
            rcases lm8 with lm8 | lm8
            · subst lm8
              refine ⟨?_, ?_⟩
              · intro l2
                by_cases lm8: l2 = l
                · subst lm8
                  simp
                  left
                  exact lm6
                · simp [lm8]
                  constructor
                  · intro lm9
-/
/-
          constructor
          · intro lm8
            have lm9 := lm8 r
            simp at lm9
            have lm10 := lm8 r2
            simp at lm10
            refine ⟨?_, ?_⟩
            · intro l2
              constructor
              · intro lm11
                rcases lm11 with lm11 | lm11
                · subst lm11
-/
/-
          have lm8 := h.leftListToRightFinset?_eq_none_iff.mp lm7
          rcases lm8 with ⟨l2, lm8, lm9⟩
          intro lm10
          specialize lm10 l
          simp at lm10
          simp [lm7] at lm2
          refine lm2 ?_
-/
/-
          rcases lm10 with lm10 | lm10
          · have lm11 := IsBiUnique.rightUnique lm10 lm6
            subst lm11
            clear lm10
            exists r
            simp
-/
/-
      rcases Option.eq_none_or_eq_some (pcs.right? l) with lm6 | lm6
      · simp [lm6]
        intro lm7
        replace lm6 := h.right?_eq_none_iff_forall_not_rel.mp lm6
        specialize lm7 l
        simp at lm7
        simp [lm6] at lm7
      · rcases lm6 with ⟨r2, lm6⟩
        simp [lm6]
        replace lm6 := h.rel_of_right?_eq_some lm6
        rcases Option.eq_none_or_eq_some (pcs.leftListToRightFinset? ls) with lm7 | lm7
        · simp [lm7]
          intro lm8
          specialize lm8 l
          simp at lm8
          rcases lm8 with lm8 | lm8
          · exists r
            simp [lm8]
            simp [lm7] at lm2
-/

    --
/-
  induction ls using Finset.induction with
  | empty =>
    induction rs using Finset.induction with
    | empty =>
      simp
      rfl
    | insert r rs lm1 lm2 =>
      simp
      conv => lhs; lhs; change pcs.leftListToRightFinset? []
      simp [leftListToRightFinset?, Finset.ext_iff]
      intro lm3
      specialize lm3 r
      simp at lm3
  | insert l ls lm1 lm2 =>
    simp [leftFinsetToRightFinset?, leftMultisetToRightFinset?]
    have := Multiset.ndinsert
-/
/-
    induction rs using Finset.cons_induction with
    | empty =>
      simp []
-/

/-
theorem leftFinsetToRightFinset?_eq_some_iff_setlikeHEq [IsBiUnique rel] [DecidableEq αr] (h: IsPartialCongruence pcs rel) {ls: Finset αl} {rs: Finset αr}
  : (pcs.leftFinsetToRightFinset? ls = .some rs) ↔ (SetLikeHEq rel (Finset αl) (Finset αr) ls rs) := by
  rcases ls with ⟨ls, lm1⟩
  rcases rs with ⟨rs, lm2⟩
  dsimp [leftFinsetToRightFinset?, leftMultisetToRightFinset?]
  cases ls using Quotient.ind
  rename_i ls
  dsimp only [Quotient.liftOn_mk]
  induction ls with
  | nil =>
    simp [leftListToRightFinset?]
    cases rs using Quotient.ind
    rename_i rs
    rcases rs with _ | ⟨r, rs⟩
    · simp
      dsimp [setLikeHEq_def, setHEq_def, setOfLeftSet, setOfRightSet]
      simp
    · dsimp [setLikeHEq_def, setHEq_def, setOfLeftSet, setOfRightSet]
      have lm3: (∅: Finset αr) ≠ ⟨↑(r :: rs), lm2⟩ := by
        intro lm3
        rewrite [Finset.ext_iff] at lm3
        specialize lm3 r
        simp at lm3
      simp [lm3]
      intro lm4
      simp [Set.ext_iff] at lm4
      specialize lm4 (.ofSum (.inr r))
      simp at lm4
  | cons l ls lm3 =>
    dsimp [leftListToRightFinset?]
    generalize lm4: pcs.right? l = r?
    generalize lm5: pcs.leftListToRightFinset? ls = rs?
    rcases r? with _ | ⟨r⟩
    · simp
      have lm6 := h.right?_eq_none_iff_forall_not_rel.mp lm4
      intro lm7
      dsimp [setLikeHEq_def, setHEq_def, setOfLeftSet, setOfRightSet] at lm7
      simp [Set.ext_iff] at lm7
      specialize lm7 (.ofSum (.inl l))
      simp [lnl_eq_lnr_iff_rel, lm6] at lm7
    · dsimp
      rcases rs? with _ | ⟨rs⟩
      · simp
        have lm6 := h.rel_of_right?_eq_some lm4
        intro lm7
        dsimp [setLikeHEq_def, setHEq_def, setOfLeftSet, setOfRightSet] at lm7
        simp [Set.ext_iff] at lm7
        specialize lm7 (.ofSum (.inr r))
        simp [inr_eq_inl_iff_rel, lm6] at lm7
        simp [ofSum_eq_iff_sumEquivGen, sumEquivGen_inr_inr_iff] at lm7
        simp at lm1
        rcases lm1 with ⟨lm1, lm8⟩
        simp [lm5] at lm3
        specialize lm3 lm8
        revert lm3
        dsimp [setLikeHEq_def, setHEq_def, setOfLeftSet, setOfRightSet]
        simp [Set.ext_iff]
-/
        --dsimp [setLikeHEq_def, setHEq_def, setOfLeftSet, setOfRightSet] at lm3
        --simp [Set.ext_iff] at lm3

#check Finset.cons


end IsPartialCongruence


end Nemonuri.Relations.Heterogeneous

end
