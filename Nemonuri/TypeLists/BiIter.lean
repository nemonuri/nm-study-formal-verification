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

inductive BiIter.{u, u2} (D: Type u → Type u → Sort u2) : List (Type u) → Sort _ where
  | single (Ty: Type u) : BiIter D [Ty]
  | cons (Ty1 Ty2: Type u) (tys: List (Type u)) (d: D Ty1 Ty2) : BiIter D (Ty1::tys) → BiIter D (Ty1::Ty2::tys)

inductive BiIter₂.{u, u2} (D: Type u → Type u → Sort u2) : List (Type u) → Sort _ where
  | single (Ty: Type u) : BiIter₂ D [Ty]
  | cons (Ty1 Ty2: Type u) (tys: List (Type u)) : BiIter D (Ty1::Ty2::tys) → BiIter₂ D (Ty2::tys) → BiIter₂ D (Ty1::Ty2::tys)

universe u u2

namespace BiIter

variable {D: Type u → Type u → Sort u2}

def count {tys: List (Type u)} : BiIter D tys → Nat
  | .single _ => 0
  | .cons _ _ _ _ bi => bi.count + 1

theorem count_eq_types_length_sub_one {tys: List (Type u)} {bi: BiIter D tys} : bi.count = tys.length - 1 := by
  cases bi with
  | single _ => dsimp [count]
  | cons _ _ _ _ bi =>
    dsimp [count]
    have lm1 := bi.count_eq_types_length_sub_one
    rw [lm1]
    dsimp

theorem count_add_one_eq_types_length {tys: List (Type u)} {bi: BiIter D tys} : bi.count + 1 = tys.length := by
  have lm1 := bi.count_eq_types_length_sub_one
  replace lm1 := congrArg (· + 1) lm1
  refine Eq.trans lm1 ?_
  refine Nat.sub_add_cancel ?_
  rcases bi <;> simp

theorem not_nil (bi: BiIter D []) : False := nomatch bi

def elimNil {C: Sort*} (bi: BiIter D []) : C := bi.not_nil |>.elim


abbrev getAt (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (bi: BiIter D (Ty1 :: mid ++ Ty2 :: post)) : D Ty1 Ty2 :=
  match mid, bi with
  | [], .cons _ _ _ d _ => d
  | _::mid, .cons _ _ _ _ bi => BiIter.getAt Ty1 mid Ty2 post bi


def getOfIterSum (Ty: Type u) (tys: List (Type u)) (bi: BiIter D (Ty::tys)) (isum: IterSum (Ty::tys)) (ofRefl: (Ty: Type u) → D Ty Ty) : D Ty isum.ValType :=
  match tys, bi, isum with
  | [], (.single _), (.ofVal _ _ _) => ofRefl Ty
  | _::tys2, (.cons _ _ _ d bi2), isum =>
  match isum with
  | .ofVal _ _ _ => ofRefl Ty
  | .cons _ _ isum =>
  match isum with
  | .ofVal _ _ _ => d
  | .cons _ _ isum => getOfIterSum Ty tys2 bi2 (.cons Ty tys2 isum) ofRefl


end BiIter


namespace BiIter₂

variable {D: Type u → Type u → Sort u2}

def count {tys: List (Type u)} : BiIter₂ D tys → Nat
  | .single _ => 0
  | .cons _ _ _ bi1 bi2 => bi2.count + bi1.count

theorem count_eq_types_length_pow {tys: List (Type u)} {bi: BiIter₂ D tys} : bi.count = ((tys.length - 1) * tys.length) / 2 := by
  cases bi with
  | single _ => dsimp [count]
  | cons _ _ _ bi1 bi2 =>
    dsimp [count]
    have lm1 := bi1.count_eq_types_length_sub_one
    have lm2 := bi2.count_eq_types_length_pow
    dsimp at lm1 lm2
    conv =>
      rhs
      conv =>
        arg 1
        conv => arg 2; rw [Nat.add_assoc]
        rw [Nat.mul_add]
      rw [Nat.add_mul_div_right _ _ (Nat.zero_lt_succ 1)]
      dsimp
      conv =>
        lhs
        arg 1
        rw [Nat.mul_comm]
      rw [← lm2, ← lm1]


def getAt (pre: List (Type u)) (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (bi: BiIter₂ D (pre ++ Ty1 :: mid ++ Ty2 :: post)) : D Ty1 Ty2 :=
  match pre, mid, bi with
  | [], [], .cons _ _ _ bi1 _ => BiIter.getAt Ty1 [] Ty2 post bi1
  | [], Ty3::mid, .cons _ _ _ bi1 _ => BiIter.getAt Ty1 (Ty3::mid) Ty2 post bi1
  | [_], mid, .cons _ _ _ _ bi2 => BiIter₂.getAt [] Ty1 mid Ty2 post bi2
  | _::Ty4::pre, mid, .cons _ _ _ _ bi2 => BiIter₂.getAt (Ty4::pre) Ty1 mid Ty2 post bi2

theorem not_nil (bi: BiIter₂ D []) : False := nomatch bi

def elimNil {C: Sort*} (bi: BiIter₂ D []) : C := bi.not_nil |>.elim


def getOfIterSum {tys: List (Type u)} (bi: BiIter₂ D tys) (isum1 isum2: IterSum tys) (ofRefl: (Ty: Type u) → D Ty Ty) (ofSymm: (Ty1 Ty2: Type u) → D Ty1 Ty2 → D Ty2 Ty1) : D isum1.ValType isum2.ValType :=
  match tys, bi with
  | [Ty], (.single _) =>
    match isum1, isum2 with
    | .ofVal _ _ _, .ofVal _ _ _ => ofRefl Ty
  | Ty1::Ty2::tys2, .cons _ _ _ bi1 bi2 =>
    match isum1, isum2 with
    | .ofVal _ _ _, isum2 => BiIter.getOfIterSum Ty1 (Ty2::tys2) bi1 isum2 ofRefl
    | isum1, .ofVal _ _ _ => BiIter.getOfIterSum Ty1 (Ty2::tys2) bi1 isum1 ofRefl |> ofSymm _ _
    | .cons _ _ isum1, .cons _ _ isum2 => getOfIterSum bi2 isum1 isum2 ofRefl ofSymm
    --BiIter.getOfIterSum Ty2 tys2
/-
  | Ty1::Ty2::tys2, .cons _ _ _ (.cons _ _ _ d bi1) bi2 =>
    match isum1, isum2 with
    | .ofVal _ _ _, .ofVal _ _ _ => ofRefl Ty1
    | .ofVal _ _ _, .cons _ _ (.ofVal _ _ _) => d
    | .ofVal _ _ _, .cons _ _ (.cons _ _ isum2) => BiIter.getOfIterSum Ty1 tys2 bi1 (.cons Ty1 tys2 isum2) ofRefl
    | .cons _ _ (.ofVal _ _ _), .ofVal _ _ _ => ofSymm _ _ d
    | .cons _ _ (.ofVal _ _ _), .cons _ _ (.ofVal _ _ _) => ofRefl Ty2
    | .cons _ _ (.ofVal _ _ v1), .cons _ _ (.cons _ _ isum2) => getOfIterSum bi2 (.ofVal Ty2 tys2 v1) (.cons Ty2 tys2 isum2) ofRefl ofSymm
    | .cons _ _ (.cons _ _ isum1), .ofVal _ _ _ => BiIter.getOfIterSum Ty1 tys2 bi1 (.cons Ty1 tys2 isum1) ofRefl |> ofSymm _ _
    | .cons _ _ (.cons _ _ isum1), .cons _ _ (.ofVal _ _ v2) => getOfIterSum bi2 (.cons Ty2 tys2 isum1) (.ofVal Ty2 tys2 v2) ofRefl ofSymm
    | .cons _ _ (.cons _ _ isum1), .cons _ _ (.cons _ _ isum2) => getOfIterSum bi2 (.cons _ _ isum1) (.cons _ _ isum2) ofRefl ofSymm
-/



end BiIter₂


--def IterRel (tys: List (Type u)) : Type _ := BiIter (fun Ty1 Ty2 => Ty1 → Ty2 → Prop) tys


def IterRel₂ (tys: List (Type u)) : Type _ := BiIter₂ (fun Ty1 Ty2 => Ty1 → Ty2 → Prop) tys


namespace IterRel₂

abbrev SumRel {tys: List (Type u)} (irel: IterRel₂ tys) (isum1 isum2: IterSum tys) : Prop :=
  BiIter₂.getOfIterSum irel isum1 isum2 (fun _ _ _ => True) (fun _ _ rel => flip rel) isum1.val isum2.val

@[defeq]
theorem sumRel_def {tys: List (Type u)} {irel: IterRel₂ tys} {isum1 isum2: IterSum tys}
  : SumRel irel isum1 isum2 = BiIter₂.getOfIterSum irel isum1 isum2 (fun _ _ _ => True) (fun _ _ rel => flip rel) isum1.val isum2.val :=
  rfl

namespace SumRel

--variable {tys: List (Type u)}

@[refl]
protected theorem refl {tys: List (Type u)} (irel: IterRel₂ tys) (isum: IterSum tys) : irel.SumRel isum isum := by
  dsimp [SumRel]
  cases irel with
  | single _ =>
    cases isum with
    | ofVal _ =>
      unfold BiIter₂.getOfIterSum
      simp only
    | cons _ _ isum =>
      exact isum.elimNil
  | cons _ Ty2 tys bi1 bi2 =>
    cases isum with
    | ofVal _ =>
      unfold BiIter₂.getOfIterSum
      simp only
      rcases bi1
      unfold BiIter.getOfIterSum
      simp only
    | cons _ _ isum =>
      unfold BiIter₂.getOfIterSum
      simp only
      exact SumRel.refl bi2 isum

/-
protected theorem symm {tys: List (Type u)} (irel: IterRel₂ tys) (isum1 isum2: IterSum tys) (req: irel.SumRel isum1 isum2) : irel.SumRel isum2 isum1 := by
  dsimp [SumRel] at ⊢ req
  cases irel with
  | single _ =>
    cases
-/

end SumRel

/-
abbrev RelAt (pre: List (Type u)) (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (irel: IterRel₂ (pre ++ Ty1 :: mid ++ Ty2 :: post)) : Ty1 → Ty2 → Prop :=
  BiIter₂.getAt pre Ty1 mid Ty2 post irel
-/



--abbrev SumRelAt (pre: List (Type u)) (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (irel: IterRel₂ (pre ++ Ty1 :: mid ++ Ty2 :: post))

/-
inductive SumRelGen : (tys: List (Type u)) → IterRel₂ tys → IterSum tys → IterSum tys → Prop where
  | rel (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (v1: Ty1) (v2: Ty2)
        (irel: IterRel₂ (Ty1 :: mid ++ Ty2 :: post)) (req: IterRel₂.RelAt [] Ty1 mid Ty2 post irel v1 v2)
    : SumRelGen (Ty1 :: mid ++ Ty2 :: post) irel (.ofVal Ty1 (mid ++ Ty2 :: post) v1) (IterSum.append (Ty1 :: mid) (.ofVal Ty2 post v2))
  | cons (Ty1 Ty2: Type u) (tys: List (Type u)) (irel1: IterRel (Ty1::Ty2::tys)) (irel2: IterRel₂ (Ty2::tys)) (isum1 isum2: IterSum (Ty2::tys))
    : (SumRelGen (Ty2::tys) irel2 isum1 isum2) → SumRelGen (Ty1::Ty2::tys) (.cons Ty1 Ty2 tys irel1 irel2) (.cons Ty1 _ isum1) (.cons Ty1 _ isum2)
-/



end IterRel₂



  --(Ty: Type u) (tys: List (Type u)) (ds: BiIter D (Ty::tys))
  --| single (Ty: Type u) : BiIter₂ D [Ty]
  --| cons (Ty1 Ty2: Type u) (tys: List (Type u)) (ds: BiIter)


  --| ofVal (Ty1 Ty2: Type u) (d: D Ty1 Ty2) : BiIter D [Ty1, Ty2]
  --| cons (Ty: Type u)

/-
inductive IterHRel.{u} : List (Type u) → Type _ where
  | single (Head: Type u) : IterHRel [Head]
  | cons (Head1 Head2: Type u) (tail: List (Type u)) (rel: Head1 → Head2 → Prop) : IterHRel (Head1 :: tail) → IterHRel (Head2 :: tail) → IterHRel (Head1 :: Head2 :: tail)
-/

/-
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


end IterTrans



namespace IterSumRel

variable {tys: List (Type u)} {irel: IterHRel tys}


end IterSumRel




end IterHRel
-/

end Nemonuri.TypeLists

end
