module


public import Nemonuri.TypeLists.IterSum

@[expose] public section

set_option autoImplicit false


namespace Nemonuri.Relations.Heterogeneous

def CanTransfer {Ty1 Ty2 Ty3: Type*} (rel1: Ty1 → Ty2 → Prop) (rel2: Ty2 → Ty3 → Prop) : Prop := ∀⦃v2: Ty2⦄, (∃(v1: Ty1), rel1 v1 v2) ↔ (∃(v3: Ty3), rel2 v2 v3)

variable {Ty1 Ty2 Ty3: Type*} {rel1: Ty1 → Ty2 → Prop} {rel2: Ty2 → Ty3 → Prop}

@[defeq]
theorem canTransfer_def : CanTransfer rel1 rel2 = ∀(v2: Ty2), (∃(v1: Ty1), rel1 v1 v2) ↔ (∃(v3: Ty3), rel2 v2 v3) := rfl

namespace CanTransfer

theorem right_exists_of_left (h: CanTransfer rel1 rel2) {v1 v2} (req: rel1 v1 v2) : ∃v3, rel2 v2 v3 := by
  dsimp [canTransfer_def] at h
  specialize h v2
  rcases h with ⟨lm1, lm2⟩
  simp at lm1
  exact lm1 v1 req

theorem left_exists_of_right (h: CanTransfer rel1 rel2) {v2 v3} (req: rel2 v2 v3) : ∃v1, rel1 v1 v2 := by
  dsimp [canTransfer_def] at h
  specialize h v2
  rcases h with ⟨lm1, lm2⟩
  simp at lm2
  exact lm2 v3 req

end CanTransfer

def Comp {Ty1 Ty2 Ty3: Type*} (rel1: Ty1 → Ty2 → Prop) (rel2: Ty2 → Ty3 → Prop) (v1: Ty1) (v3: Ty3) : Prop := ∃v2, rel1 v1 v2 ∧ rel2 v2 v3

end Nemonuri.Relations.Heterogeneous


namespace Nemonuri.TypeLists


inductive IterHRel.{u} : List (Type u) → Type _ where
  | single (Head: Type u) : IterHRel [Head]
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (rel: Head1 → Head2 → Prop) : IterHRel (Head1 :: tail) → IterHRel (Head2 :: tail) → IterHRel (Head1 :: Head2 :: tail)


namespace IterHRel

universe u

abbrev types {tys: List (Type u)} (_: IterHRel tys) : List (Type u) := tys


theorem not_nil (irel: IterHRel []) : False := nomatch irel

def elimNil {C: Sort*} (irel: IterHRel []) : C := irel.not_nil |>.elim

def headRel {Ty1 Ty2: Type u} {tys: List (Type u)} : IterHRel (Ty1::Ty2::tys) → Ty1 → Ty2 → Prop
  | .cons _ _ _ rel _ _ => rel

def tailPair {Ty1 Ty2: Type u} {tys: List (Type u)} : (IterHRel (Ty1::Ty2::tys)) → (IterHRel (Ty1::tys)) × (IterHRel (Ty2::tys))
  | .cons _ _ _ _ irel1 irel2 => ⟨irel1, irel2⟩

def swap {Ty1 Ty2: Type u} {tys: List (Type u)} : (IterHRel (Ty1::Ty2::tys)) → IterHRel (Ty2::Ty1::tys)
  | .cons _ _ _ rel irel1 irel2 => .cons _ _ _ (flip rel) irel2 irel1


/-
  match tys1, tys2, req, irel with
  | [Ty], tys2, req, .single _ => irel |> cast (by)
-/

/-
def append (tys1: List (Type u)) (Ty: Type u) (tys2: List (Type u)) (iter1: IterHRel (tys1 ++ tys2)) (iter2: IterHRel (Ty::tys2)) : IterHRel (tys1 ++ Ty::tys2) :=
  match tys1 with
  | [] => iter2
  | [Ty1] => .cons Ty1 Ty tys2
-/







inductive IterRelDep.{u2} (D: (Ty1 Ty2: Type u) → (rel: Ty1 → Ty2 → Prop) → Sort u2) : (tys: List (Type u)) → (IterHRel tys) → Sort _ where
  | single (Head: Type u) : IterRelDep D [Head] (.single Head)
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (rel: Head1 → Head2 → Prop) (dep: D _ _ rel)
         (iter1: IterHRel (Head1 :: tail)) (iterD1: IterRelDep D (Head1 :: tail) iter1)
         (iter2: IterHRel (Head2 :: tail)) (iterD2: IterRelDep D (Head2 :: tail) iter2)
         : IterRelDep D (Head1 :: Head2 :: tail) (.cons Head1 Head2 tail rel iter1 iter2)

inductive IterRelDep₃.{u2} (D: (Ty1 Ty2 Ty3: Type u) → (rel1: Ty1 → Ty2 → Prop) → (rel2: Ty1 → Ty3 → Prop) → (rel3: Ty2 → Ty3 → Prop) → Sort u2) : (tys: List (Type u)) → (IterHRel tys) → Sort _ where
  | single (Ty: Type u) : IterRelDep₃ D [Ty] (.single Ty)
  | double (Ty1 Ty2: Type u) (rel: Ty1 → Ty2 → Prop) : IterRelDep₃ D [Ty1, Ty2] (.cons Ty1 Ty2 [] rel (.single _) (.single _))
  | cons (Ty1 Ty2 Ty3: Type u) (tail: List (Type u)) (rel1: Ty1 → Ty2 → Prop) (rel2: Ty1 → Ty3 → Prop) (rel3: Ty2 → Ty3 → Prop) (dep: D _ _ _ rel1 rel2 rel3)
         (iter1: IterHRel (Ty1 :: tail)) (iterD1: IterRelDep₃ D _ iter1)
         (iter2: IterHRel (Ty2 :: tail)) (iterD2: IterRelDep₃ D _ iter2)
         (iter3: IterHRel (Ty3 :: tail)) (iterD3: IterRelDep₃ D _ iter3)
         : IterRelDep₃ D (Ty1::Ty2::Ty3::tail) (.cons Ty1 Ty2 (Ty3::tail) rel1 (.cons _ _ tail rel2 iter1 iter3) (.cons _ _ tail rel3 iter2 iter3))



def RelAt (pre: List (Type u)) (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (irel: IterHRel (pre ++ Ty1 :: mid ++ Ty2 :: post)) : Ty1 → Ty2 → Prop :=
  match pre with
  | [] =>
    match mid with
    | [] =>
      match irel with
      | .cons _ _ _ rel _ _ => rel
    | Ty3::mid =>
      match irel with
      | .cons _ _ _ _ irel _ => RelAt [] Ty1 mid Ty2 post irel
  | [Ty3] =>
    match irel with
    | .cons _ _ _ _ _ irel => RelAt [] Ty1 mid Ty2 post irel
  | Ty3::Ty4::pre =>
    match irel with
    | .cons _ _ _ _ _ irel => RelAt (Ty4::pre) Ty1 mid Ty2 post irel

#print RelAt._unary




--inductive RelAt (pre: List (Type u)) (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (irel: IterHRel (pre ++ Ty1 :: mid ++ Ty2 :: post))

def OfFinLt {tys: List (Type u)} (iter: IterHRel tys) (i1 i2: Fin tys.length) (req: i1 < i2) : iter.types[i1] → iter.types[i2] → Prop :=
  match tys, iter with
  | [Ty], .single _ => False.elim (by rcases i1 with ⟨i1, lm1⟩; rcases i2 with ⟨i2, lm2⟩; simp at lm1 lm2 req; simp [lm1, lm2] at req)
  | Ty1::Ty2::tys, .cons _ _ _ rel iter1 iter2 =>
  let ⟨i1, lm1⟩ := i1
  let ⟨i2, lm2⟩ := i2
  match i1 with
  | 0 =>
    match i2 with
    | 0 => False.elim (by simp at req)
    | 1 => rel
    | i2 + 2 =>
      OfFinLt iter1 ⟨0, (by simp)⟩ ⟨(i2 + 1), (by simp at lm2 ⊢; exact lm2)⟩ (by rw [Fin.mk_lt_mk]; simp) --|> cast (by dsimp)
  | i1 + 1 =>
    match i2 with
    | 0 | 1 => False.elim (by rw [Fin.mk_lt_mk] at req; simp at req)
    | i2 + 2 =>
      OfFinLt iter2 ⟨i1, (by simp at lm1 ⊢; exact lm1)⟩ ⟨(i2 + 1), (by simp at ⊢ lm2; exact lm2)⟩ (by rw [Fin.mk_lt_mk] at ⊢ req; simpa using req)


inductive ReflSymmOfFin {tys: List (Type u)} (iter: IterHRel tys) (i1: Fin tys.length) (v1: iter.types[i1]) (i2: Fin tys.length) (v2: iter.types[i2]) : Prop where
  | rel (req1: i1 < i2) (req2: OfFinLt iter i1 i2 req1 v1 v2)
  | refl (req1: i1 = i2) (req2: v1 ≍ v2)
  | rel_symm (req1: i2 < i1) (req2: OfFinLt iter i2 i1 req1 v2 v1)
/-
  | rel (i1 i2: Fin tys.length) (req: i1 < i2) (v1: iter.types[i1]) (v2: iter.types[i2]) : ReflSymmOfFin iter i1 v1 i2 v2
  | refl (i: Fin tys.length) (v: iter.types[i]) : ReflSymmOfFin iter i v i v
  | rel_symm (i1 i2: Fin tys.length) (req: i1 < i2) (v1: iter.types[i1]) (v2: iter.types[i2]) : ReflSymmOfFin iter i2 v2 i1 v1
-/
/-
  symm (i1: Fin tys.length) (v1: iter.types[i1]) (i2: Fin tys.length) (v2: iter.types[i2]) (req: i2 < i1)
        : ReflSymmOfFin iter i1 v1 i2 v2 → ReflSymmOfFin iter i2 v2 i1 v1
-/

def IterSumRel {tys: List (Type u)} (iter: IterHRel tys) (isum1 isum2: IterSum tys) : Prop :=
  iter.ReflSymmOfFin isum1.valIndexFin isum1.valAsGetElem isum2.valIndexFin isum2.valAsGetElem

@[defeq]
theorem iterSumRel_def {tys: List (Type u)} {iter: IterHRel tys} {isum1 isum2: IterSum tys}
  : IterSumRel iter isum1 isum2 = iter.ReflSymmOfFin isum1.valIndexFin isum1.valAsGetElem isum2.valIndexFin isum2.valAsGetElem :=
  rfl


namespace IterSumRel

variable {tys: List (Type u)} {irel: IterHRel tys}

@[refl]
protected theorem refl (isum: IterSum tys) : irel.IterSumRel isum isum := by
  dsimp [iterSumRel_def]
  exact .refl rfl (HEq.refl _)

open IterSum in
theorem ofVal_ofVal_to_val_eq {Ty: Type u} {v1 v2: Ty} {irel: IterHRel (Ty::tys)} (h: IterSumRel irel (ofVal Ty tys v1) (ofVal Ty tys v2)) : v1 = v2 := by
  dsimp [iterSumRel_def] at h
  rcases h <;> rename_i lm1 lm2
  · simp [ofVal_valIndexFin_eq_zero] at lm1
  · simp [valAsGetElem, val, valAt] at lm2
    exact eq_of_heq lm2
  · simp [ofVal_valIndexFin_eq_zero] at lm1


theorem ofVal_ofVal_iff_val_eq {Ty: Type u} {v1 v2: Ty} {irel: IterHRel (Ty::tys)} : IterSumRel irel (.ofVal Ty tys v1) (.ofVal Ty tys v2) ↔ (v1 = v2) := by
  constructor
  · exact ofVal_ofVal_to_val_eq
  · intro lm1
    subst lm1
    rfl


open IterSum in
@[symm]
protected theorem symm {isum1 isum2: IterSum tys} (h: irel.IterSumRel isum1 isum2) : irel.IterSumRel isum2 isum1 := by
  dsimp [iterSumRel_def] at ⊢ h
  cases h with
  | rel lm1 lm2 => exact .rel_symm lm1 lm2
  | refl lm1 lm2 => exact .refl lm1.symm lm2.symm
  | rel_symm lm1 lm2 => exact .rel lm1 lm2


instance : Std.Refl irel.IterSumRel := ⟨IterSumRel.refl⟩

instance : Std.Symm irel.IterSumRel := ⟨fun _ _ => IterSumRel.symm⟩


end IterSumRel




abbrev IterBiUnique {tys: List (Type u)} (irel: (IterHRel tys)) : Type _ := IterRelDep (fun _ _ rel => Relator.BiUnique rel) tys irel

@[defeq]
theorem iterBiUnique_def {tys: List (Type u)} {irel: (IterHRel tys)} : IterBiUnique irel = IterRelDep (fun _ _ rel => Relator.BiUnique rel) tys irel :=
  rfl

abbrev IterDecidableRel {tys: List (Type u)} (irel: (IterHRel tys)) : Type _ := IterRelDep (fun _ _ rel => DecidableRel rel) tys irel

@[defeq]
theorem iterDecidableRel_def {tys: List (Type u)} {irel: (IterHRel tys)} : IterDecidableRel irel = IterRelDep (fun _ _ rel => DecidableRel rel) tys irel :=
  rfl





open Relations.Heterogeneous in
abbrev IterTrans {tys: List (Type u)} (irel: (IterHRel tys)) : Type _ := IterRelDep₃ (fun _ _ _ rel1 rel2 rel3 => CanTransfer rel1 rel3 ∧ Comp rel1 rel3 = rel2 ) tys irel

open Relations.Heterogeneous in
@[defeq]
theorem iterTrans_def {tys: List (Type u)} {irel: (IterHRel tys)} : IterTrans irel = IterRelDep₃ (fun _ _ _ rel1 rel2 rel3 => CanTransfer rel1 rel3 ∧ Comp rel1 rel3 = rel2 ) tys irel := rfl


namespace IterTrans

variable {tys: List (Type u)} {irel: (IterHRel tys)}

/-
theorem ofFinLt_trans (i1 i2 i3: Fin tys.length) (req1: i1 < i2) (req2: i2 < i3) (v1 v2 v3) (req3: OfFinLt irel i1 i2 req1 v1 v2) (req4: OfFinLt irel i2 i3 req2 v2 v3)
  : OfFinLt irel i1 i3 (Nat.lt_trans req1 req2) v1 v3 := by
  cases irel with
  | single Ty =>
    dsimp at i1 i2 i3
    rcases i1 with ⟨i1, lm1⟩
    rcases i2 with ⟨i2, lm2⟩
    simp at lm1 lm2
    subst lm1 lm2
    simp at req1
  | cons Ty1 Ty2 tys rel irel1 irel2 =>
    dsimp at i1 i2 i3
    cases irel2 with
    | single _ =>
      dsimp at i1 i2 i3
      rcases i1 with ⟨i1, lm1⟩
      rcases i2 with ⟨i2, lm2⟩
      rcases i3 with ⟨i3, lm3⟩
      simp at req1 req2
      have lm4 (i: Nat) (req: i < 2) : i = 0 ∨ i = 1 := by
        rcases i with _ | ⟨i⟩
        · left; rfl
        · rewrite [Nat.add_one_lt_add_one_iff] at req
          simp at req
          right
          rw [req]
      rcases (lm4 _ lm1) with lm_s | lm_s <;> (subst lm_s)
      <;> rcases (lm4 _ lm2) with lm_s | lm_s <;> (subst lm_s)
      <;> rcases (lm4 _ lm3) with lm_s | lm_s <;> (subst lm_s)
      <;> simp_all only [Nat.lt_irrefl, Nat.not_lt_zero]
    | cons _ Ty3 tys rel2 irel2 irel3 =>
      dsimp at i1 i2 i3
      unfold OfFinLt at req3 req4 ⊢
      simp at req3 req4
-/
      --simp [OfFinLt] at req3 req4



end IterTrans



--OfFinLt {tys: List (Type u)} (iter: IterHRel tys) (i1 i2: Fin tys.length) (req: i1 < i2) : iter.types[i1] → iter.types[i2] → Prop :=


--abbrev IterHTrans {tys: List (Type u)} (irel: (IterHRel tys)) : Type _ := IterRelDep₂ (fun _ Ty2 _ rel1 rel2 => ∀(v2: Ty2), (∃v1, rel1 v1 v2) ↔ (∃v3, rel2 v2 v3)) tys irel


         --(iter1: IterHRel (Ty2 :: tail)) (iterD1: IterRelDep₂ D (Ty2 :: tail) iter1)
         --(iter2: IterHRel (Ty3 :: tail)) (iterD2: IterRelDep₂ D (Ty3 :: tail) iter2)
         --: IterRelDep₂ D (Ty1 :: Ty2 :: Ty3 :: tail) (.cons Ty1 Ty2 (Ty3::tail) rel1 (.cons Ty1 Ty3 ) )
--(.cons Ty2 Ty3 tail rel2 iter1 iter2)
/-
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (rel: Head1 → Head2 → Prop) (iter1: IterHRel (Head1 :: tail)) (iter2: IterHRel (Head2 :: tail))
    : IterRelDep₂ D (Head1 :: Head2 :: tail) (.cons Head1 Head2 tail rel iter1 iter2)
-/
/-
  | cons_cons (Head1 Head2 Head3: Type u) (tail: List (Type u)) (rel1: Head1 → Head2 → Prop) (rel2: Head2 → Head3 → Prop) (dep₂: D _ _ _ rel1 rel2)
              (iter1: IterHRel (Head2 :: tail)) (iter2: IterHRel (Head3 :: tail))
-/

namespace IterSumRel

variable {tys: List (Type u)} {irel: IterHRel tys}

/-
open IterSum in
protected theorem trans (ibu: irel.IterBiUnique) (isum1 isum2 isum3: IterSum tys)
  (h1: irel.IterSumRel isum1 isum2) (h2: irel.IterSumRel isum2 isum3) : irel.IterSumRel isum1 isum3 := by
  dsimp [iterSumRel_def] at h1 h2 ⊢
  cases h1 with
  | rel lm1 lm2 =>
    cases h2 with
    | rel lm3 lm4 =>
-/
/-
  induction isum1 with
  | ofVal Ty1 tys v1 =>
    cases isum2 with
    | ofVal _ _ v2 =>
      cases isum3 with
      | ofVal _ _ v3 =>
-/

/-
  dsimp [iterBiUnique_def] at ibu
  cases ibu with
  | single Ty =>
    dsimp [iterSumRel_def] at h1 h2 ⊢
    rcases isum1 --(try (refine IterSum.elimNil ?_; assumption))
    <;> rcases isum2
    <;> rcases isum3
    <;> try (refine IterSum.elimNil ?_; assumption)
    rename_i v1 v2 v3
    dsimp [IterSum.types] at h1 h2
-/
    --dsimp only [valAsGetElem] at h1 h2
    --rw [ofVal_valIndexFin_eq_zero] at h1 h2
    --rewrite [ofVal_valIndex_eq_zero] at h1 h2
    --generalize lm1: (ofVal Ty [] v1) = isum1 at h1 h2
    --generalize lm2: (ofVal Ty [] v2) = isum2 at h1 h2
    --have lm3 :=
/-
    cases h1 with
    | rel _ _ lm1 =>
      dsimp [valIndexFin] at lm1
      rw [Fin.mk_lt_mk] at lm1
      dsimp [valIndex] at lm1
      unfold valIndexAt at lm1
      simp only at lm1
      exact Nat.not_lt_zero _ lm1 |>.elim
    | refl => exact h2
    | symm _ _ _ _ lm1 =>
-/




end IterSumRel




end IterHRel

end Nemonuri.TypeLists

end
