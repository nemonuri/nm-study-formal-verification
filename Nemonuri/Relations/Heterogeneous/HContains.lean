module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.SetLikeHEq

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} {rel: αl → αr → Prop}


variable (rel) in
def hcontains [DecidableRel rel] (l: αl) (rs: List αr) : Bool := rs.any (fun r => rel l r)

section HContains

variable [DecidableRel rel] {l: αl} {rs: List αr}

@[defeq, simp]
theorem hcontains_nil : hcontains rel l [] = .false := by dsimp [hcontains]

@[defeq, simp]
theorem hcontains_cons {r rs} : hcontains rel l (r :: rs) = (rel l r || hcontains rel l rs) := by
  dsimp [hcontains]

variable (rel l) in
theorem hcontains_respects_perm (rs1 rs2: List αr) (req: rs1.Perm rs2) : hcontains rel l rs1 = hcontains rel l rs2 := by
  induction req with
  | nil => dsimp
  | @cons r rs1 rs2 lm1 lm2 => simp [lm2]
  | swap r1 r2 rs =>
    dsimp
    conv => lhs; rw [Bool.or_left_comm]
  | trans _ _ lm1 lm2 => exact lm1.trans lm2

end HContains

variable (rel) in
def isHSublist [DecidableRel rel] (ls: List αl) (rs: List αr) : Bool := ls.all (fun l => hcontains rel l rs)

section HSublist

variable [DecidableRel rel] {rs: List αr}

@[defeq, simp]
theorem isHSublist_nil : isHSublist rel [] rs = .true := by dsimp [isHSublist]

@[defeq, simp]
theorem isHSublist_cons {l ls} : isHSublist rel (l :: ls) rs = ((hcontains rel l rs) && isHSublist rel ls rs) := by dsimp [isHSublist]

variable (rel) in
theorem isHSublist_respects_perm_right (ls: List αl) (rs1 rs2: List αr) (req: rs1.Perm rs2) : isHSublist rel ls rs1 = isHSublist rel ls rs2 := by
  induction req with
  | nil => dsimp
  | @cons r rs1 rs2 lm1 lm2 =>
    dsimp [isHSublist]
    rw [Bool.eq_iff_iff]
    simp [or_iff_not_imp_left]
    constructor
    · intro lm3 l lm4 lm5
      specialize lm3 l lm4 lm5
      have lm6 := hcontains_respects_perm rel l rs1 rs2 lm1
      exact lm6.symm.trans lm3
    · intro lm3 l lm4 lm5
      specialize lm3 l lm4 lm5
      have lm6 := hcontains_respects_perm rel l rs1 rs2 lm1
      exact lm6.trans lm3
  | swap r1 r2 rs =>
    dsimp [isHSublist]
    rw [Bool.eq_iff_iff]
    simp [or_iff_not_imp_left]
    constructor <;> (
      intro lm1 l lm2 lm3 lm4
      specialize lm1 l lm2 lm4 lm3
      exact lm1 )
  | trans _ _ lm1 lm2 => exact lm1.trans lm2

theorem isHSublist_respects_perm (ls1 ls2: List αl) (req1: ls1.Perm ls2) (rs1 rs2: List αr) (req2: rs1.Perm rs2) : isHSublist rel ls1 rs1 = isHSublist rel ls2 rs2 := by
  induction req1 with
  | nil => dsimp
  | @cons l ls1 ls2 lm1 lm2 =>
    simp
    have lm3 := hcontains_respects_perm rel l rs1 rs2 req2
    simp only [lm3, lm2]
  | swap l1 l2 ls =>
    dsimp
    conv =>
      lhs
      rw [Bool.and_left_comm]
      conv => arg 1; rw [hcontains_respects_perm rel l1 rs1 rs2 req2]
      arg 2
      conv => arg 1; rw [hcontains_respects_perm rel l2 rs1 rs2 req2]
      conv => arg 2; rw [isHSublist_respects_perm_right rel ls rs1 rs2 req2]
  | @trans ls1 ls2 ls3 lm1 lm2 lm3 lm4 =>
    rewrite [isHSublist_respects_perm_right rel ls1 rs1 rs2 req2] at lm3 ⊢
    rewrite [isHSublist_respects_perm_right rel ls2 rs1 rs2 req2] at lm4
    exact lm3.trans lm4

end HSublist







end Nemonuri.Relations.Heterogeneous
