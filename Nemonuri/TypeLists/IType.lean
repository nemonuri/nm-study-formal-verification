module


public import Nemonuri.TypeLists.IterNonempty


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TypeLists



inductive IType.{u} : List (Type u) → Nat → Type _ where
  | ofVal (Head: Type u) (tail: List (Type u)) (v: Head) : IType (Head::tail) 0
  | cons (Head: Type u) (tail: List (Type u)) (i: Nat) (ival: IType tail i) : IType (Head::tail) (i + 1)


namespace IType

universe u

abbrev types {tys: List (Type u)} {i: Nat} (_: IType tys i) : List (Type u) := tys

abbrev index {tys: List (Type u)} {i: Nat} (_: IType tys i) : Nat := i

def depth {tys: List (Type u)} {i: Nat} (ival: IType tys i) : Nat :=
  match ival with
  | .ofVal _ _ _ => 0
  | .cons _ _ _ ival => (ival.depth) + 1

theorem depth_eq_index {tys: List (Type u)} {i: Nat} (ival: IType tys i)
  : ival.depth = ival.index := by
  dsimp [index]
  rcases ival with _ | ⟨_,_,_,ival⟩
  · dsimp [depth]
  · dsimp [depth]
    simp only [Nat.add_right_cancel_iff]
    exact ival.depth_eq_index

def height {tys: List (Type u)} {i: Nat} (ival: IType tys i) : Nat :=
  match ival with
  | .ofVal _ tail _ => tail.length
  | .cons _ _ _ ival => ival.height


theorem index_add_height_add_one_eq_types_length {tys: List (Type u)} {i: Nat} (ival: IType tys i)
  : ival.index + ival.height + 1 = ival.types.length := by
  dsimp [index, types]
  rcases ival with _ | ⟨_,_,_,ival⟩
  · dsimp [height]
    simp
  · dsimp [height]
    have lm1 := ival.index_add_height_add_one_eq_types_length
    dsimp [index, types] at lm1
    simp [← lm1]
    omega


def ofPrePost (pre: List (Type u)) (post: List (Type u)) {Ty: Type u} (v: Ty) : IType (pre ++ (Ty :: post)) pre.length :=
  match pre with
  | [] => .ofVal _ post v
  | Head::pre =>
    let iv : IType (pre ++ (Ty :: post)) pre.length := ofPrePost pre post v
    .cons Head _ _ iv


theorem not_nil (i: Nat) : (IType [] i) → False := by
  intro iv
  rcases iv

def elimNil {C: Sort _} {i: Nat} (iv: IType [] i) : C := iv.not_nil i |>.elim

theorem index_lt_types_length {tys: List (Type u)} {i: Nat} (iv: IType tys i) : iv.index < iv.types.length := by
  dsimp [index, types]
  rcases iv with _ | ⟨_,_,_,iv⟩
  · exact Nat.zero_lt_succ _
  · simp
    exact iv.index_lt_types_length


def val {tys: List (Type u)} {i: Nat} (iv: IType tys i) : tys[i]'(iv.index_lt_types_length) :=
  match iv with
  | .ofVal _ _ v => v
  | .cons _ _ _ iv => iv.val

@[ext]
protected def ext {tys: List (Type u)} {i: Nat} (iv1 iv2: IType tys i) (req: iv1.val = iv2.val) : iv1 = iv2 := by
  rcases iv1 with ⟨_,_,v1⟩ | ⟨_,_,_,iv1⟩
  <;> rcases iv2 with ⟨_,_,v2⟩ | ⟨_,_,_,iv2⟩
  · dsimp [val] at req
    rw [req]
  · dsimp [val] at req
    simp
    exact IType.ext iv1 iv2 req



def ofFin (tys: List (Type u)) (i: Fin tys.length) (v: tys[i]) : IType tys ↑i :=
  match tys with
  | [] => i.elim0
  | Head::tys =>
  match i with
  | ⟨i, lm1⟩ =>
  match i with
  | 0 => .ofVal Head tys v
  | i + 1 =>
    have lm2 : i < tys.length := by simpa using lm1
    let iv := ofFin tys ⟨i, lm2⟩ v
    .cons Head _ _ iv

protected noncomputable def choose (tys: List (Type u)) (i: Nat) (req1: IterNonempty tys) (req2: i < tys.length) : IType tys i :=
  ofFin tys ⟨i, req2⟩ (Classical.choice (req1.nonempty_fin ⟨i, req2⟩))

noncomputable def chooseAlt (tys: List (Type u)) (req: IterNonempty tys) (i: Fin tys.length) : IType tys ↑i :=
  IType.choose tys i.val req i.is_lt

/-
theorem index_eq_of_heq (tys: List (Type u)) (req1: IterNonempty tys) (i1 i2: Nat) (iv1: IType tys i1) (iv2: IType tys i2) (req2: iv1 ≍ iv2) : i1 = i2 := by
  rcases tys with _ | ⟨Ty, tys⟩
  · exact iv1.elimNil
  · have lm1 := iv1.index_lt_types_length
    have lm2 := iv2.index_lt_types_length
    dsimp [index, types] at lm1 lm2
    rcases iv1 with ⟨_,_,v1⟩ | _
    · rcases iv2 with _ | ⟨_,_,i2,iv2⟩
      · rfl
      · simp at lm2
        rcases req1 with _ | ⟨_,_,_,req1⟩
        have lm3 := index_eq_of_heq tys req1
-/
        --have lm3 := index_eq_of_heq tys 0 i2
/-
    induction i1 with
    | zero =>
      induction i2 with
      | zero => rfl
      | succ i2 lm3 =>
-/
/-
    induction i1 with
    | zero =>
      induction i2 with
      | zero => rfl
      | succ i2 lm1 =>
        rcases iv2
-/

/-
theorem chooseAlt_inj (tys: List (Type u)) (req1: IterNonempty tys) (i1 i2: Fin tys.length) (req2: chooseAlt tys req1 i1 = chooseAlt tys req1 i2) : i1 = i2 :=


theorem not_types_length_le_index (tys: List (Type u)) (i: Nat) (req: tys.length ≤ i) : (IType tys i) → False := by
  rcases tys with _ | ⟨_, tys⟩
  · intro iv
    exact iv.elimNil
  · intro iv
    simp at req
    have lm1 := iv.index_lt_types_length
    dsimp [index, types] at lm1
    have lm2 : i < i := Trans.trans lm1 req
    exact Nat.lt_irrefl i lm2


theorem fin_index_eq_of_itype_eq {tys: List (Type u)} (req1: IterNonempty tys) (i1 i2: Fin tys.length) (req2: IType tys i1 = IType tys i2) : i1 = i2 := by
  rcases i1 with ⟨i1, lm1⟩
  rcases i2 with ⟨i2, lm2⟩
  have (eq := lm3) iv1 := IType.choose tys i1 req1 lm1
-/

/-
theorem fin_index_eq_of_itype_eq {tys: List (Type u)} (req1: IterNonempty tys) (i1 i2: Fin tys.length) (req2: IType tys i1 = IType tys i2) : i1 = i2 := by
  rcases i1 with ⟨i1, lm1⟩
  rcases i2 with ⟨i2, lm2⟩
  have (eq := lm5) iv1 := IType.choose tys i1 req1 lm1
  have (eq := lm6) iv2 := IType.choose tys i2 req1 lm2
  rcases i1 with _ | ⟨i1⟩
  · rcases i2 with _ | ⟨i2⟩
    · rfl
    ·
-/
  --rcases Nat.ne_iff_lt_or_gt.mp lm3 with lm4 | lm4
  --·
  --simp [Nat.ne_iff_lt_or_gt] at lm1



/-
theorem fin_index_eq_of_itype_eq {tys: List (Type u)} (req1: IterNonempty tys) (i1 i2: Fin tys.length) (req2: IType tys ↑i1 = IType tys ↑i2) : i1 = i2 := by
  rcases req1.nonempty_fin i1 with ⟨v1⟩
  rcases req1.nonempty_fin i2 with ⟨v2⟩
  have (eq := lm1) iv1 := ofFin tys i1 v1
  have (eq := lm2) iv2 := ofFin tys i2 v2
  have lm3 := iv1.depth_eq_index
-/

/-
  rcases tys with _ | ⟨Ty, tys⟩
  · exact i1.elim0
  · rcases req1 with _ | ⟨_,_,v,lm3⟩
    rcases i1 with ⟨i1, lm1⟩
    rcases i2 with ⟨i2, lm2⟩
    simp at lm1 lm2 ⊢
-/
/-

-/

--theorem itype_ne_of_index_ne {tys: List (Type u)} {i1 i2: Nat} (req1: IterNonempty tys) (req2: i1 ≠ i2) : IType tys i1 ≠ IType tys i2 := by





end IType


end Nemonuri.TypeLists

end
