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

universe u u2

namespace BiIter

variable {D: Type u → Type u → Sort u2}


def count {tys: List (Type u)} : BiIter D tys → Nat
  | .single _ => 0
  | .cons _ _ _ _ bi => bi.count + 1

@[defeq, simp]
theorem count_single {Ty: Type u} : (@BiIter.single D Ty).count = 0 := rfl

@[defeq, simp]
theorem count_cons {Ty1 Ty2: Type u} {tys: List (Type u)} {d: D Ty1 Ty2} {bi: BiIter D (Ty1::tys)}
  : (BiIter.cons Ty1 Ty2 tys d bi).count = bi.count + 1 :=
  rfl


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

theorem add_one_lt_types_length_of_lt_count {tys: List (Type u)} {bi: BiIter D tys} {i: Nat} (req: i < bi.count) : (i + 1) < tys.length :=
  calc
    (i+1) < _ := Nat.add_lt_add_right req 1
    _ = _ := count_add_one_eq_types_length


theorem lt_types_length_of_lt_count {tys: List (Type u)} {bi: BiIter D tys} {i: Nat} (req: i < bi.count) : i < tys.length :=
  calc
    i < _ := Nat.lt_add_one i
    _ < _ := add_one_lt_types_length_of_lt_count req


macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| apply add_one_lt_types_length_of_lt_count; assumption)
--macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| apply lt_types_length_of_lt_count; assumption)

theorem not_nil (bi: BiIter D []) : False := nomatch bi

def elimNil {C: Sort*} (bi: BiIter D []) : C := bi.not_nil |>.elim

theorem length_pos {tys: List (Type u)} {bi: BiIter D tys} : 0 < tys.length := by
  rcases tys with _ | _
  · exact bi.elimNil
  · simp

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| apply length_pos; assumption)


def getAt (Ty1: Type u) (mid: List (Type u)) (Ty2: Type u) (post: List (Type u)) (bi: BiIter D (Ty1 :: mid ++ Ty2 :: post)) : D Ty1 Ty2 :=
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

section GetOfIterSumSection

variable {Ty: Type u} {ofRefl: (Ty: Type u) → D Ty Ty}

@[defeq, simp]
theorem getOfIterSum_nil_eq_refl (v: Ty) : getOfIterSum Ty [] (.single Ty) (.ofVal Ty [] v) ofRefl = ofRefl Ty := by
  unfold getOfIterSum
  simp only


variable {Ty2: Type u} {tys2: List (Type u)} {d: D Ty Ty2} {bi2: BiIter D (Ty :: tys2)}

@[defeq, simp]
theorem getOfIterSum_ofVal_eq_refl (v: Ty) : getOfIterSum Ty (Ty2::tys2) (.cons Ty Ty2 tys2 d bi2) (.ofVal _ _ v) ofRefl = ofRefl Ty := by
  unfold getOfIterSum
  simp only

@[defeq, simp]
theorem getOfIterSum_ofVal_cons_eq (v2: Ty2) : getOfIterSum Ty (Ty2::tys2) (.cons Ty Ty2 tys2 d bi2) (.cons Ty _ (.ofVal Ty2 tys2 v2)) ofRefl = d := by
  unfold getOfIterSum
  simp only

@[defeq, simp]
theorem getOfIterSum_cons_cons_eq (isum2: IterSum tys2)
  : getOfIterSum Ty (Ty2::tys2) (.cons Ty Ty2 tys2 d bi2) (.cons Ty _ (.cons Ty2 _ isum2)) ofRefl = getOfIterSum Ty tys2 bi2 (.cons Ty tys2 isum2) ofRefl := by
  conv => lhs; unfold getOfIterSum; simp only

end GetOfIterSumSection


section HeadTailSection

variable {Ty1 Ty2: Type u} {tys: List (Type u)}

def head : BiIter D (Ty1::Ty2::tys) → D Ty1 Ty2
  | .cons _ _ _ d _ => d

def tail : BiIter D (Ty1::Ty2::tys) → BiIter D (Ty1::tys)
  | .cons _ _ _ _ bi => bi

@[defeq, simp]
theorem head_def (d: D Ty1 Ty2) (bi: BiIter D (Ty1::tys)) : (BiIter.cons Ty1 Ty2 tys d bi).head = d := rfl

@[defeq, simp]
theorem tail_def (d: D Ty1 Ty2) (bi: BiIter D (Ty1::tys)) : (BiIter.cons Ty1 Ty2 tys d bi).tail = bi := rfl

theorem tail_count_eq_count_sub_one (bi: BiIter D (Ty1::Ty2::tys)) : bi.tail.count = bi.count - 1 := by
  rcases bi
  dsimp

end HeadTailSection


section GetSection

def get {tys: List (Type u)} (bi: BiIter D tys) (i: Nat) (req: i < bi.count) : D tys[0] tys[i + 1] :=
  match tys, bi, i with
  | [Ty], (.single _), _ => False.elim (by dsimp at req; exact Nat.not_lt_zero _ req)
  | Ty1::Ty2::tys, .cons _ _ _ d _, 0 => d
  | Ty1::Ty2::tys, .cons _ _ _ _ bi, i + 1 => get bi i (by simpa using req)

variable {Ty1 Ty2: Type u} {tys: List (Type u)} {bi: BiIter D (Ty1::Ty2::tys)}

@[simp]
theorem get_zero (req: 0 < bi.count) : bi.get 0 req = bi.head := by
  rcases bi
  unfold get
  simp only
  dsimp

@[simp]
theorem get_add_one (i: Nat) (req: (i + 1) < bi.count) : bi.get (i + 1) req = bi.tail.get i (by simp [tail_count_eq_count_sub_one]; omega) := by
  rcases bi
  dsimp at ⊢ req
  conv => lhs; unfold get; simp only

end GetSection

end BiIter


inductive BiIter₂ (D: Type u → Type u → Sort u2) : List (Type u) → Sort _ where
  | single (Ty: Type u) : BiIter₂ D [Ty]
  | cons (Ty1 Ty2: Type u) (tys: List (Type u)) : BiIter D (Ty1::Ty2::tys) → BiIter₂ D (Ty2::tys) → BiIter₂ D (Ty1::Ty2::tys)

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
    | .ofVal _ _ _, .ofVal _ _ _ => ofRefl Ty1
    | .ofVal _ _ _, .cons _ _ isum2 => BiIter.getOfIterSum Ty1 (Ty2::tys2) bi1 (.cons _ _ isum2) ofRefl
    | .cons _ _ isum1, .ofVal _ _ _ => BiIter.getOfIterSum Ty1 (Ty2::tys2) bi1 (.cons _ _ isum1) ofRefl |> ofSymm _ _
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
section GetOfIterSumSection

variable {ofRefl: (Ty: Type u) → D Ty Ty} {ofSymm: (Ty1 Ty2: Type u) → D Ty1 Ty2 → D Ty2 Ty1}

@[defeq, simp]
theorem getOfIterSum_single_eq_refl {Ty: Type u} (v1 v2: Ty) : getOfIterSum (.single Ty) (.ofVal _ _ v1) (.ofVal _ _ v2) ofRefl ofSymm = ofRefl Ty := by
  unfold getOfIterSum
  simp only

variable {Ty1 Ty2: Type u} {tys2: List (Type u)} {bi1 : BiIter D (Ty1 :: Ty2 :: tys2)} {bi2 : BiIter₂ D (Ty2 :: tys2)}

@[defeq, simp]
theorem getOfIterSum_ofVal_ofVal_eq_refl (v1 v2: Ty1)
  : getOfIterSum (.cons _ _ _ bi1 bi2) (.ofVal _ _ v1) (.ofVal _ _ v2) ofRefl ofSymm = ofRefl Ty1 := by
  unfold getOfIterSum
  simp only

@[defeq, simp]
theorem getOfIterSum_ofVal_cons_eq (v1: Ty1) (isum2 : IterSum (Ty2 :: tys2))
  : getOfIterSum (.cons _ _ _ bi1 bi2) (.ofVal _ _ v1) (.cons _ _ isum2) ofRefl ofSymm = BiIter.getOfIterSum Ty1 (Ty2::tys2) bi1 (.cons _ _ isum2) ofRefl := by
  unfold getOfIterSum
  simp only

@[defeq, simp]
theorem getOfIterSum_cons_ofVal_eq (isum1 : IterSum (Ty2 :: tys2)) (v2: Ty1)
  : getOfIterSum (.cons _ _ _ bi1 bi2) (.cons _ _ isum1) (.ofVal _ _ v2) ofRefl ofSymm = ofSymm _ _ (BiIter.getOfIterSum Ty1 (Ty2::tys2) bi1 (.cons _ _ isum1) ofRefl) := by
  unfold getOfIterSum
  simp only

@[defeq, simp]
theorem getOfIterSum_cons_cons_eq (isum1 isum2 : IterSum (Ty2 :: tys2))
  : getOfIterSum (.cons _ _ _ bi1 bi2) (.cons _ _ isum1) (.cons _ _ isum2) ofRefl ofSymm = getOfIterSum bi2 isum1 isum2 ofRefl ofSymm := by
  conv => lhs; unfold getOfIterSum; simp


end GetOfIterSumSection


section HeadTailSection

variable {Ty1 Ty2: Type u} {tys: List (Type u)}

def head : BiIter₂ D (Ty1::Ty2::tys) → BiIter D (Ty1::Ty2::tys)
  | .cons _ _ _ bi _ => bi

def tail : BiIter₂ D (Ty1::Ty2::tys) → BiIter₂ D (Ty2::tys)
  | .cons _ _ _ _ bi => bi

@[defeq, simp]
theorem head_def (bi1: BiIter D (Ty1::Ty2::tys)) (bi2: BiIter₂ D (Ty2::tys)) : (BiIter₂.cons _ _ _ bi1 bi2).head = bi1 := rfl

@[defeq, simp]
theorem tail_def (bi1: BiIter D (Ty1::Ty2::tys)) (bi2: BiIter₂ D (Ty2::tys)) : (BiIter₂.cons _ _ _ bi1 bi2).tail = bi2 := rfl

end HeadTailSection


section LengthSection

def length {tys: List (Type u)} (bi: BiIter₂ D tys) : Nat :=
  match tys, bi with
  | [_], .single _ => 0
  | _::_::_, .cons _ _ _ _ bi => bi.length + 1


variable {Ty1 Ty2: Type u} {tys: List (Type u)}

@[defeq, simp]
theorem length_single : (@single D Ty1).length = 0 := rfl

@[defeq, simp]
theorem length_cons (bi₁: BiIter D (Ty1::Ty2::tys)) (bi₂: BiIter₂ D (Ty2::tys)) : (cons Ty1 Ty2 tys bi₁ bi₂).length = bi₂.length + 1 := rfl


theorem cons_cons_length_pos (bi: BiIter₂ D (Ty1::Ty2::tys)) : 0 < bi.length := by
  rcases bi
  simp

theorem length_eq_types_length_sub_one {tys: List (Type u)} (bi: BiIter₂ D tys) : bi.length = tys.length - 1 := by
  rcases bi with _ | ⟨_,_,_,bi₁,bi⟩
  · dsimp
  · dsimp
    have lm1 := length_eq_types_length_sub_one bi
    dsimp at lm1
    rw [lm1]

theorem head_count_eq_length {Ty1 Ty2: Type u} {tys: List (Type u)} (bi: BiIter₂ D (Ty1::Ty2::tys)) : bi.head.count = bi.length := by
  rcases bi with _ | ⟨_,_,_,bi₁,bi⟩
  dsimp
  rw [bi₁.count_eq_types_length_sub_one, bi.length_eq_types_length_sub_one]
  dsimp

theorem tail_length_eq_bi_length_sub_one {Ty1 Ty2: Type u} {tys: List (Type u)} (bi: BiIter₂ D (Ty1::Ty2::tys)) : bi.tail.length = bi.length - 1 := by
  rcases bi with _ | ⟨_,_,_,bi₁,bi⟩
  dsimp

theorem add_one_lt_types_length_of_lt_length {tys: List (Type u)} {bi: BiIter₂ D tys} {i: Nat} (req: i < bi.length) : (i + 1) < tys.length := by
  rewrite [length_eq_types_length_sub_one] at req
  omega

/-
  rcases bi <;> simp at req
  rcases i with _ | ⟨i⟩
  · simp
  · simp at req ⊢
    have lm1 := lt_types_length_of_lt_length req
    dsimp at lm1
    exact lm1
-/

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| apply add_one_lt_types_length_of_lt_length; assumption)

end LengthSection


section GetSection


def get {tys: List (Type u)} (bi: BiIter₂ D tys) (i: Nat) (req: i < bi.length) : BiIter D (tys.drop i) :=
  match tys, bi, i with
  | [_], .single _ , _ => False.elim (by simp at req)
  | Ty1::Ty2::tys, .cons _ _ _ bi₁ bi, i =>
  match i with
  | 0 => bi₁
  | i + 1 => bi.get i (by simpa using req)

variable {Ty1 Ty2: Type u} {tys: List (Type u)}

attribute [local simp] length_eq_types_length_sub_one in
theorem get_zero_eq_head (bi₂: BiIter₂ D (Ty1::Ty2::tys)) : bi₂.get 0 (by simp) = bi₂.head := by
  rcases bi₂
  dsimp
  unfold get
  simp only

attribute [local simp] tail_length_eq_bi_length_sub_one in
theorem get_add_one_eq_tail_get (bi₂: BiIter₂ D (Ty1::Ty2::tys)) (i: Nat) (req: i + 1 < bi₂.length)
  : bi₂.get (i + 1) req = bi₂.tail.get i (by simp; omega) := by
  rcases bi₂
  dsimp
  conv => lhs; unfold get; simp only


attribute [simp] get_zero_eq_head get_add_one_eq_tail_get


theorem get_count_eq_length_sub {tys: List (Type u)} (bi: BiIter₂ D tys) (i: Nat) (req: i < bi.length) : (bi.get i req).count = bi.length - i := by
  rcases bi with _ | ⟨_,_,_,bi1,bi⟩
  · simp at req
  · simp at req ⊢
    rcases i with _ | ⟨i⟩
    · simp
      rw [bi1.count_eq_types_length_sub_one, bi.length_eq_types_length_sub_one]
      dsimp
    · simp at ⊢ req
      exact get_count_eq_length_sub bi i req

/-
def get {tys: List (Type u)} (bi: BiIter₂ D tys) (i1 i2: Nat) (req1: i1 < bi.length) (req2: i2 < bi.length) (req3: i1 < i2) : D tys[i1] tys[i2] :=
  match tys, bi, i1, i2 with
  | [_], .single _, _, _ => False.elim (by simp at req1)
  | Ty1::Ty2::tys, .cons _ _ _ bi₁ bi, i1, i2 =>
  match i1, i2 with
  | 0, 0 => False.elim (by simp at req3)
  | 0, i2 + 1 => bi₁.get i2 (by
    rw [bi₁.count_eq_types_length_sub_one]
    simp at ⊢ req2
    have lm1 := lt_types_length_of_lt_length req2
    dsimp at lm1
    exact lm1 )
  | i1 + 1, 0 => False.elim (by simp at req3)
  | i1 + 1, i2 + 1 => bi.get i1 i2 (by simpa using req1) (by simpa using req2) (by simpa using req3)


variable {Ty1 Ty2: Type u} {tys: List (Type u)}

@[simp]
theorem get_zero_add_one (bi: BiIter₂ D (Ty1::Ty2::tys)) (i2: Nat) (req: i2 + 1 < bi.length)
  : bi.get 0 (i2 + 1) (bi.cons_cons_length_pos) req (Nat.zero_lt_succ i2) = bi.head.get i2 (by rw [head_count_eq_length]; omega) := by
  rcases bi with _ | ⟨_,_,_,bi₁,bi⟩
  dsimp
  unfold get
  simp only

@[simp]
theorem get_add_one_add_one (bi: BiIter₂ D (Ty1::Ty2::tys)) (i1 i2: Nat) (req1: i1 + 1 < bi.length) (req2: i2 + 1 < bi.length) (req3: i1 < i2)
  : bi.get (i1 + 1) (i2 + 1) req1 req2 (Nat.add_lt_add_right req3 1) = bi.tail.get i1 i2 (by rw [bi.tail_length_eq_bi_length_sub_one]; omega) (by rw [bi.tail_length_eq_bi_length_sub_one]; omega) req3 := by
  rcases bi with _ | ⟨_,_,_,bi₁,bi⟩
  dsimp
  conv => lhs; unfold get; simp only
-/


end GetSection


def get₂ {tys: List (Type u)} (bi: BiIter₂ D tys) (i1 i2: Nat) (req: i1 + i2 < bi.length) : D (tys[i1]'(by rw [bi.length_eq_types_length_sub_one] at req; omega)) tys[i1 + i2 + 1] :=
  let bi1 := bi.get i1 (by omega)
  bi1.get i2 (by subst bi1; rw [get_count_eq_length_sub]; omega) |> cast (by
    subst bi1
    simp
    conv => lhs; arg 2; simp only [← Nat.add_assoc])

section Get2Section

variable {Ty1 Ty2: Type u} {tys: List (Type u)}

@[simp]
theorem get₂_zero_zero_eq_head_head (bi: BiIter₂ D (Ty1::Ty2::tys))
  : bi.get₂ 0 0 (bi.cons_cons_length_pos) = bi.head.head := by
  dsimp [get₂]
  simp

protected theorem get₂_zero_eq_head_get₂.aux1 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i2: Nat} (req: i2 < bi.length) : 0 + i2 < bi.length := by
  rw [Nat.zero_add i2]
  exact req

protected theorem get₂_zero_eq_head_get₂.aux2 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i2: Nat} (req: i2 < bi.length) : i2 < bi.head.count := by
  rw [bi.head_count_eq_length]
  exact req

protected theorem get₂_zero_eq_head_get₂.aux3 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i2: Nat} (req: i2 < bi.length)
  : D Ty1 ((Ty2::tys)[i2]'(by revert req; simp [bi.length_eq_types_length_sub_one])) = D Ty1 ((Ty1::Ty2::tys)[0 + i2 + 1]'(by revert req; simp [bi.length_eq_types_length_sub_one])) := by
  simp

theorem get₂_zero_eq_head_get (bi: BiIter₂ D (Ty1::Ty2::tys)) (i2: Nat) (req: i2 < bi.length)
  : bi.get₂ 0 i2 (get₂_zero_eq_head_get₂.aux1 req) = (Equiv.cast (get₂_zero_eq_head_get₂.aux3 req)) (bi.head.get i2 (get₂_zero_eq_head_get₂.aux2 req)) := by
  rcases bi with _ | ⟨_,_,_,bi1,bi⟩
  dsimp [get₂]
  congr




protected theorem get₂_zero_add_one_eq.aux {bi: BiIter₂ D (Ty1::Ty2::tys)} {i2: Nat} (req: (i2 + 1) < bi.length) : i2 < (bi.get 0 (bi.cons_cons_length_pos)).tail.count := by
  rcases bi
  simp at ⊢ req
  rw [BiIter.count_eq_types_length_sub_one]
  rewrite [length_eq_types_length_sub_one] at req
  dsimp at ⊢ req
  exact req


theorem get₂_zero_add_one_heq (bi: BiIter₂ D (Ty1::Ty2::tys)) (i2: Nat) (req: (i2 + 1) < bi.length)
  : bi.get₂ 0 (i2 + 1) (by simpa using req) ≍ (bi.get 0 (bi.cons_cons_length_pos)).tail.get i2 (get₂_zero_add_one_eq.aux req) := by
  rcases bi
  dsimp [get₂]
  simp


protected theorem get₂_add_one_zero_eq.aux {bi: BiIter₂ D (Ty1::Ty2::tys)} {i1: Nat} (req: (i1 + 1) < bi.length) : i1 < bi.tail.length := by
  rw [bi.tail_length_eq_bi_length_sub_one]
  omega

@[simp]
theorem get₂_add_one_zero_eq (bi: BiIter₂ D (Ty1::Ty2::tys)) (i1: Nat) (req: (i1 + 1) < bi.length)
  : bi.get₂ (i1 + 1) 0 req = bi.tail.get₂ i1 0 (get₂_add_one_zero_eq.aux req) := by
  rcases bi
  dsimp [get₂]
  congr


protected theorem get₂_add_one_eq.aux1 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i1 i2: Nat} (req: (i1 + i2 + 1) < bi.length) : i1 + i2 < bi.tail.length := by
  rw [bi.tail_length_eq_bi_length_sub_one]
  omega

protected theorem get₂_add_one_eq.aux2 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i1 i2: Nat} (req: (i1 + i2 + 1) < bi.length) : i1 < tys.length + 1 := by
  rewrite [bi.length_eq_types_length_sub_one] at req
  simp at req
  omega

protected theorem get₂_add_one_eq.aux3 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i1 i2: Nat} (req: (i1 + i2 + 1) < bi.length) : i1 + i2 < tys.length := by
  rewrite [bi.length_eq_types_length_sub_one] at req
  simpa using req

protected theorem get₂_add_one_eq.aux4 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i1 i2: Nat} (req: (i1 + i2 + 1) < bi.length) : (i1 + 1 + i2) < (Ty2 :: tys).length := by
  have lm1 := get₂_add_one_eq.aux3 req
  conv => lhs; rw [Nat.add_right_comm]
  simpa using lm1

protected theorem get₂_add_one_eq.aux5 {bi: BiIter₂ D (Ty1::Ty2::tys)} {i1 i2: Nat} (req: (i1 + i2 + 1) < bi.length)
  : have := get₂_add_one_eq.aux2 req; have := get₂_add_one_eq.aux3 req; have := get₂_add_one_eq.aux4 req;
    D (Ty2 :: tys)[i1] (tys)[i1 + i2] = D (Ty2 :: tys)[i1] (Ty2 :: tys)[i1 + 1 + i2] := by
  dsimp
  conv => rhs; arg 2; arg 2; rw [Nat.add_right_comm]
  dsimp

theorem get₂_add_one_eq (bi: BiIter₂ D (Ty1::Ty2::tys)) (i1 i2: Nat) (req: (i1 + i2 + 1) < bi.length)
  : bi.get₂ (i1 + 1) i2 (by omega) = (Equiv.cast (get₂_add_one_eq.aux5 req)) (bi.tail.get₂ i1 i2 (get₂_add_one_eq.aux1 req)) := by
  rcases bi with _ | ⟨_,_,_,_,bi⟩
  revert req
  simp
  intro req
  dsimp [get₂]
  simp
  congr


end Get2Section

end BiIter₂





end Nemonuri.TypeLists

end
