module

public import Nemonuri.Functions.LiftableEmbedding.Equiv
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding

universe uu us


structure SubBundled (Univ: Sort uu) where
  Sub: Sort us
  liftableEmbedding: LiftableEmbedding Sub Univ

namespace SubBundled

variable {Univ: Sort uu}

@[ext]
protected theorem ext {sb1 sb2: SubBundled Univ} (req1: sb1.Sub = sb2.Sub) (req2: sb1.liftableEmbedding.embed ≍ sb2.liftableEmbedding.embed) : sb1 = sb2 := by
  rcases sb1 with ⟨s1, lm1⟩
  rcases sb2 with ⟨s2, lm2⟩
  dsimp at req1
  subst req1
  simp at req2 ⊢
  exact LiftableEmbedding.embed_ext req2

@[ext]
protected theorem ext_lift {sb1 sb2: SubBundled Univ}
  (req1: sb1.Sub = sb2.Sub)
  (req2: ∀(uv: Univ), sb1.liftableEmbedding.IsLiftable uv ↔ sb2.liftableEmbedding.IsLiftable uv)
  (req3: ∀(uv: Univ) (req3_1: sb1.liftableEmbedding.IsLiftable uv) (req3_2: sb2.liftableEmbedding.IsLiftable uv), req3_1.lift ≍ req3_2.lift)
  : sb1 = sb2 := by
  rcases sb1 with ⟨Sub1, lem1⟩
  rcases sb2 with ⟨Sub2, lem2⟩
  dsimp at req1
  subst req1
  simp at req2 req3 ⊢
  simp [DFunLike.ext_iff]
  intro s1
  let uv : Univ := lem1 s1
  specialize req2 uv
  specialize req3 uv
  have lm1 : lem1.IsLiftable uv := by subst uv; exact IsLiftable.of_apply
  simp [lm1] at req2
  specialize req3 lm1 req2
  subst uv
  rewrite [lm1.lift_eq_self] at req3
  cases req2 using IsLiftable.induction
  rename_i s2 lm2
  conv at req3 => rhs; simp only [lm2]; rewrite [IsLiftable.lift_eq_self]
  subst req3
  exact lm2


--  (req: ∀(sv1: sb1.Sub) (sv2: sb2.Sub) (req_1: sb1.liftableEmbedding.IsLiftable (sb2.liftableEmbedding sv2) ))

def toPLifted (sb: SubBundled Univ) : SubBundled (PLift Univ) where
  Sub := sb.Sub
  liftableEmbedding := sb.liftableEmbedding.compEquiv (Equiv.refl _) (Equiv.plift.symm)

def ofPLifted (sb: SubBundled.{uu+1, us} (PLift.{uu} Univ)) : SubBundled.{uu, us} Univ where
  Sub := sb.Sub
  liftableEmbedding := sb.liftableEmbedding.compEquiv (Equiv.refl _) (Equiv.plift)


theorem ofPLifted_toPLifted_leftInverse : Function.LeftInverse ofPLifted (@toPLifted Univ) := by
  rintro ⟨Sub, lem⟩
  dsimp [toPLifted, ofPLifted]
  rfl

theorem ofPLifted_toPLifted_rightInverse : Function.RightInverse ofPLifted (@toPLifted Univ) := by
  rintro ⟨Sub, lem⟩
  dsimp [toPLifted, ofPLifted]
  rfl


def equivToPLifted : SubBundled Univ ≃ SubBundled (PLift Univ) where
  toFun := toPLifted
  invFun := ofPLifted

end SubBundled


def Interleaving (Univ: Sort uu) : Type (max uu us) := List ((SubBundled.{uu+1, us} (PLift.{uu} Univ)))

@[defeq]
theorem interleaving_def {Univ: Sort uu} : Interleaving Univ = List (SubBundled (PLift.{uu} Univ)) := rfl

namespace Interleaving

variable {Univ: Sort uu}

def equivToList : Interleaving Univ ≃ List (SubBundled (PLift Univ)) := Equiv.cast interleaving_def

def consSub (Sub: Sort us) (lem: LiftableEmbedding Sub Univ) (il: Interleaving Univ) : Interleaving Univ := il.cons (SubBundled.equivToPLifted ⟨Sub, lem⟩)

@[defeq]
theorem consSub_ofPLifted (sb: SubBundled (PLift Univ)) (il: Interleaving Univ)
  : consSub sb.ofPLifted.Sub sb.ofPLifted.liftableEmbedding il = il.cons sb :=
  rfl

@[defeq]
theorem consSub_length {Sub: Sort us} {lem: LiftableEmbedding Sub Univ} {il: Interleaving Univ}
  : (consSub Sub lem il).length = il.length + 1 := by
  dsimp [consSub]

@[defeq]
theorem consSub_length_at (Sub: Sort us) (lem: LiftableEmbedding Sub Univ) (il: Interleaving Univ)
  : (consSub Sub lem il).length = il.length + 1 :=
  consSub_length

@[elab_as_elim]
def recNilConsSub.{um}
  {motive: Interleaving.{uu, us} Univ → Sort um}
  (nil: motive [])
  (consSub: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (il: Interleaving Univ) → motive il → motive (il.consSub Sub lem))
  (il: Interleaving Univ)
  : motive il :=
  match il with
  | [] => nil
  | sb::il =>
    let sb2 := sb.ofPLifted
    consSub sb2.Sub sb2.liftableEmbedding il (recNilConsSub nil consSub il)


--#check List.issuf

def getSubBundled (il: Interleaving Univ) (i: Fin il.length) : SubBundled Univ := SubBundled.equivToPLifted.symm (il.get i)


theorem getSubBundled_eq_iff_get_eq {il1 il2: Interleaving Univ} {i1: Fin il1.length} {i2: Fin il2.length}
  : (il1.getSubBundled i1 = il2.getSubBundled i2) ↔ (il1.get i1 = il2.get i2) := by
  dsimp [getSubBundled]
  exact SubBundled.equivToPLifted.symm.injective.eq_iff


def getSub (il: Interleaving Univ) (i: Fin il.length) : Sort us := (il.getSubBundled i).Sub

@[defeq]
theorem getSub_eq_get_Sub {il: Interleaving Univ} {i: Fin il.length} : il.getSub i = (il.get i).Sub := by
  dsimp [getSub, getSubBundled, SubBundled.equivToPLifted, SubBundled.ofPLifted]






def getLiftableEmbedding (il: Interleaving Univ) (i: Fin il.length) : LiftableEmbedding (il.getSub i) Univ := (il.getSubBundled i).liftableEmbedding

section ConsSub

variable {Sub: Sort us} {lem: LiftableEmbedding Sub Univ} {il: Interleaving Univ}

theorem consSub_length_pos : 0 < (consSub Sub lem il).length := by simp [consSub_length]


@[defeq]
theorem consSub_getSub_zero : (consSub Sub lem il).getSub ⟨0, consSub_length_pos⟩ = Sub := by
  dsimp [getSub, getSubBundled, consSub]
  simp only [Equiv.symm_apply_apply]

@[defeq]
theorem consSub_getSub_zero_at (Sub: Sort us) (lem: LiftableEmbedding Sub Univ) (il: Interleaving Univ) : (consSub Sub lem il).getSub ⟨0, consSub_length_pos⟩ = Sub :=
  consSub_getSub_zero

@[defeq]
theorem consSub_getSub_succ {n: Nat} (req: n + 1 < (consSub Sub lem il).length)
  : (consSub Sub lem il).getSub ⟨n+1, req⟩ = il.getSub ⟨n, Nat.lt_of_succ_lt_succ req⟩ := by
  dsimp [consSub, getSub, getSubBundled]


end ConsSub


@[elab_as_elim]
def recIndex.{um}
  {motive: (il: Interleaving.{uu, us} Univ) → (i: Fin il.length) → Sort um}
  (zero: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (il: Interleaving.{uu, us} Univ) → motive (consSub Sub lem il) ⟨0, consSub_length_pos⟩)
  (succ: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (il: Interleaving.{uu, us} Univ) → (i: Fin il.length) → motive il i → motive (consSub Sub lem il) i.succ)
  (il: Interleaving Univ) (i: Fin il.length)
  : motive il i :=
  match il with
  | [] => i.elim0
  | sb::il2 =>
    let sb2 := sb.ofPLifted
    match i with
    | ⟨0, _⟩ => zero sb2.Sub sb2.liftableEmbedding il2
    | ⟨i2+1, lm1⟩ =>
      have lm2: i2 < il2.length := by simpa using lm1
      let i2_1 : Fin il2.length := ⟨i2, lm2⟩
      succ sb2.Sub sb2.liftableEmbedding il2 i2_1 (recIndex zero succ il2 i2_1)


attribute [- simp] List.get_eq_getElem in
@[ext]
protected theorem ext_get {il1 il2: Interleaving Univ}
  (req1: il1.length = il2.length)
  (req2: ∀(n: Nat), (req2_1: n < il1.length) → (req2_2: n < il2.length) → il1.getSub ⟨n, req2_1⟩ = il2.getSub ⟨n, req2_2⟩)
  (req3: ∀(n: Nat), (req2_1: n < il1.length) → (req2_2: n < il2.length) → (il1.getLiftableEmbedding ⟨n, req2_1⟩).embed ≍ (il2.getLiftableEmbedding ⟨n, req2_2⟩).embed)
  : il1 = il2 := by
  simp [interleaving_def, List.ext_get_iff, req1]
  intro n lm2
  have lm1 := req1.symm.subst lm2
  specialize req2 n lm1 lm2
  specialize req3 n lm1 lm2
  generalize lm3_1: (Fin.mk n lm1) = i1
  generalize lm3_2: (Fin.mk n lm2) = i2
  rewrite [lm3_1, lm3_2] at req2 req3
  have lm4: il1.getSubBundled i1 = il2.getSubBundled i2 := by
    dsimp [getSub] at req2
    dsimp [getLiftableEmbedding] at req3
    exact SubBundled.ext req2 req3
  rewrite [getSubBundled_eq_iff_get_eq] at lm4
  exact lm4



/-
  simp [SubBundled.ext_iff]
  dsimp [← getSub_eq_get_Sub]
  simp [req2]
-/


  --dsimp [getLiftableEmbedding] at req3
/-
  cases il1, i1 using recIndex with
  | zero Sub1 lem1 il1 =>
    simp at lm3_1
    subst lm3_1
    cases il2, i2 using recIndex with
    | zero Sub2 lem2 il2 =>
      simp [consSub_getSub_zero] at req2
      subst req2
-/
      --dsimp [getLiftableEmbedding, getSubBundled, consSub, List.get_eq_getElem] at req3
      --dsimp [SubBundled.equivToPLifted] at req3
      --have lm4_1 := SubBundled.ofPLifted_toPLifted_leftInverse.eq ⟨Sub1, lem1⟩
      --have lm4_2 := SubBundled.ofPLifted_toPLifted_leftInverse.eq ⟨Sub1, lem2⟩

      --simp [lm4] at req3
      --simp at req3
      --dsimp only [DFunLike.coe] at req3
      --dsimp [consSub, SubBundled.equivToPLifted, ] at req3

  --simp [← getSub_eq_get_Sub]
/-
  have lm3 := req2
  dsimp [getSub_eq_get_Sub] at lm3
  simp [lm3]
  let i1 := (Fin.mk n lm1)
-/
/-
  simp [SubBundled.ext_iff]
  simp [req1] at req2 --req3
  specialize req2 n lm1
  have lm2 := req1.symm.subst lm1
  dsimp [getSub_eq_get_Sub] at req2
  simp [req2]
  rcases lm3: List.get il2 ⟨n, lm1⟩ with ⟨Sub2, lem2⟩
  rcases lm4: List.get il1 ⟨n, lm2⟩ with ⟨Sub1, lem1⟩
  dsimp at lm3 lm4
  rewrite [lm3, lm4] at req2 ⊢
  dsimp at req2 ⊢
  subst req2
  simp [funext_iff]
  intro s1
  specialize req3 n lm2 lm1
-/
  --generalize (Fin.mk n lm2) = i1 at req3
  --generalize (Fin.mk n lm1) = i2 at req3
/-
  cases il1 using recNilConsSub with
  | nil => simp at lm2
  | consSub Sub11 lem11 il11
-/

  --dsimp [getLiftableEmbedding, getSubBundled, SubBund- led.equivToPLifted, SubBundled.ofPLifted, LiftableEmbedding.compEquiv, LiftableEmbedding.compEquivAndEmbed] at req3
  --simp only [Equiv.plift_apply] at req3
  --dsimp only [DFunLike.coe] at req3
  --conv at req3 =>
    --lhs; simp [lm4]
/-
  have lm2_1: (List.get il2 ⟨n, lm1⟩).liftableEmbedding.embed ≍ lem2.embed := by
    dsimp
    rw [lm3]
  have lm2_2: (List.get il1 ⟨n, req1.symm.subst lm1⟩).liftableEmbedding.embed ≍ lem1.embed := by
    dsimp
    rw [lm4]
  dsimp at lm2_1 lm2_2
  rewrite [lm3] at lm2_1
-/
/-
  dsimp at lm3
  simp [lm3] at req2
  rewrite [Eq.comm] at req2
  subst req2
  specialize req3 n lm1
  dsimp [getLiftableEmbedding, getSubBundled, SubBundled.equivToPLifted, SubBundled.ofPLifted, LiftableEmbedding.compEquiv, LiftableEmbedding.compEquivAndEmbed] at req3
  simp only [Equiv.plift_apply] at req3
  dsimp only [DFunLike.coe] at req3
  have lm2: (List.get il2 ⟨n, lm1⟩).liftableEmbedding.embed ≍ lem.embed := by
    dsimp
    rw [lm3]
  dsimp at lm2
  rcases lem with ⟨⟨lem,li⟩,lm4⟩
  dsimp at lm2
-/
  --have lm2 := congra

  --



  --refine Function.hfunext req2 ?_

  --intro s1 s2 lm3
  --

  --dsimp at lm4
  --simp
/-


  simp at req3
  dsimp only [DFunLike.coe] at req3
-/

  --dsimp only [DFunLike.coe] at req3
  --simp at req3
  --have := dcong

  --dsimp only [GetElem.getElem]
/-
  cases il1 using recNilConsSub with
  | nil =>
    cases il2 using recNilConsSub
    · rfl
    · simp [consSub_length] at req1
  | consSub Sub1 lem1 il1 h =>
    clear h
    simp [consSub_length] at req1 --req2 req3
    cases il2 using recNilConsSub with
    | nil => simp at req1
    | consSub Sub2 lem2 il2 h =>
      clear h
      simp [consSub_length] at req1-- req2 req3
      have lm1_1 := req2 0
      dsimp [consSub_getSub_zero] at lm1_1
      simp [consSub_length_pos] at lm1_1
      subst lm1_1
-/
      --have lm2_1 := consSub_getSub_zero_at Sub1 lem1 il1
      --have lm2_2 := consSub_getSub_zero_at Sub2 lem2 il2


      --rewrite [consSub_length] at lm2_1 lm2_2
      --rewrite [consSub_getSub_zero_at Sub1 lem1 il1] at lm1_1
      --rw [il1.consSub_getSub_zero] at lm1_1

--def getLiftableEmbedding (il: Interleaving Univ) (i: Fin il.length) : LiftableEmbedding (il.getSub i) Univ := (il.get i).of





end Interleaving

end Nemonuri.Functions.LiftableEmbedding

end
