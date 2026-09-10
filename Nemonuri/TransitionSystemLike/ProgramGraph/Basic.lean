module

public import Nemonuri.TransitionSystemLike.Basic
public import Nemonuri.PropositionalLogics.Tactic
public import Nemonuri.PropositionalLogics.Decidable

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 32

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri

@[reducible]
def setLikeOfIndicatorLike (C α: Type*) [FunLike C α Bool] : SetLike C α where
  coe c := { a | c a = .true }
  coe_injective := by
    intro c1 c2 lm1
    simp only [← DFunLike.coe_injective.eq_iff, funext_iff]
    simp [Set.ext_iff] at lm1
    exact lm1

namespace ProgramGraph

structure Eval (Var Val: Type*) where
  eval: Var → Val

instance {Var Val: Type*} : FunLike (Eval Var Val) Var Val where
  coe ev := ev.eval
  coe_injective := by rintro ⟨_⟩ ⟨_⟩; simp


class EvalLike (EC: Type*) (Var Val: outParam Type*) where
  protected coe: EC → Eval Var Val
  coe_injective: Function.Injective coe

attribute [coe, reducible] EvalLike.coe

namespace EvalLike

variable {EC Var Val: Type*} [EvalLike EC Var Val]

instance : CoeOut EC (Eval Var Val) := ⟨EvalLike.coe⟩

instance : FunLike EC Var Val where
  coe ec := (ec: Eval Var Val)
  coe_injective := DFunLike.coe_injective.comp EvalLike.coe_injective

@[defeq]
theorem coe_coe_eq_coe {ec: EC} : ((ec: Eval Var Val): Var → Val) = (ec: Var → Val) := rfl

end EvalLike

structure IsStandardType {Var Val: Type*} (dom : Var → Set Val) (EC: Type*) [EvalLike EC Var Val] : Prop where
  type_safe (ec: EC) (var: Var) : (ec var) ∈ (dom var)
  eval_exists (var: Var) (val: Val) (req: val ∈ dom var) : ∃(ec: EC), ec var = val


structure StandardTypeStruct (Var Val ValS: Type*) [SetLike ValS Val] where
  dom : Var → ValS

namespace StandardTypeStruct

variable {Var Val ValS: Type*} [SetLike ValS Val]

def IsValueSafe (s: StandardTypeStruct Var Val ValS) (var: Var) (val: Val) : Prop := val ∈ s.dom var

@[defeq]
theorem isValueSafe_def {s: StandardTypeStruct Var Val ValS} {var: Var} {val: Val}
  : s.IsValueSafe var val = (val ∈ s.dom var) :=
  rfl

def IsValueSetSafe (s: StandardTypeStruct Var Val ValS) (var: Var) (valS: ValS) : Prop := (valS: Set Val) ⊆ s.dom var

@[defeq]
theorem isValueSetSafe_def {s: StandardTypeStruct Var Val ValS} {var: Var} {valS: ValS}
  : s.IsValueSetSafe var valS = ((valS: Set Val) ⊆ s.dom var) :=
  rfl

@[defeq]
theorem isValueSetSafe_eq_isValueSafe {s: StandardTypeStruct Var Val ValS} {var: Var} {valS: ValS}
  : s.IsValueSetSafe var valS = (∀val ∈ valS, (s.IsValueSafe var val)) := by
  dsimp [isValueSafe_def, IsValueSetSafe]
  exact rfl


@[ext]
theorem value_ext {s1 s2: StandardTypeStruct Var Val ValS} (req: ∀(var: Var) (val: Val), (s1.IsValueSafe var val) ↔ (s2.IsValueSafe var val)) : s1 = s2 := by
  rcases s1 with ⟨dom1⟩
  rcases s2 with ⟨dom2⟩
  simp
  dsimp [IsValueSafe] at req
  simp only [funext_iff, SetLike.ext_iff]
  exact req

@[ext]
theorem valueSet_ext {s1 s2: StandardTypeStruct Var Val ValS} (req: ∀(var: Var) (valS: ValS), (s1.IsValueSetSafe var valS) ↔ (s2.IsValueSetSafe var valS)) : s1 = s2 := by
  rw [StandardTypeStruct.value_ext_iff]
  dsimp [isValueSetSafe_eq_isValueSafe] at req
  intro var val
  replace req := fun valS => req var valS
  have lm1 := req (s1.dom var)
  have lm2 := req (s2.dom var)
  dsimp [isValueSafe_def] at lm1 lm2
  simp at lm1 lm2
  specialize lm1 val
  specialize lm2 val
  dsimp [isValueSafe_def]
  exact Iff.intro lm1 lm2

@[ext]
theorem value_valueSet_ext {s1 s2: StandardTypeStruct Var Val ValS} (req: ∀(var: Var) (valS: ValS) (val: Val) (_: val ∈ valS), (s1.IsValueSafe var val) ↔ (s2.IsValueSafe var val)) : s1 = s2 := by
  rw [StandardTypeStruct.valueSet_ext_iff]
  intro var valS
  specialize req var valS
  dsimp [isValueSetSafe_eq_isValueSafe]
  exact forall₂_congr req



end StandardTypeStruct


structure StandardType (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val]
  extends toStruct: StandardTypeStruct Var Val ValS where
  valid: IsStandardType (SetLike.coe ∘ toStruct.dom) EC

/-
  Nemonuri.ProgramGraph.IsStandardType.type_safe : ∀ (ec : EC) (var : Var), ec var ∈ dom var
  Nemonuri.ProgramGraph.IsStandardType.eval_exists : ∀ (var : Var), ∀ val ∈ dom var, ∃ ec, ec var = val
-/

namespace StandardType

variable {EC Var Val ValS: Type*} [EvalLike EC Var Val] [SetLike ValS Val]

def IsEvalSafe (sty: StandardType EC Var Val ValS) (var: Var) (ec: EC) : Prop := sty.IsValueSafe var (ec var)

@[defeq]
theorem isEvalSafe_def {sty: StandardType EC Var Val ValS} {var: Var} {ec: EC} : sty.IsEvalSafe var ec = sty.IsValueSafe var (ec var) := rfl

theorem eval_safe {sty: StandardType EC Var Val ValS} {var: Var} {ec: EC} : sty.IsEvalSafe var ec := by
  have lm1 := sty.valid.type_safe ec var
  simp [← StandardTypeStruct.isValueSafe_def] at lm1
  dsimp [isEvalSafe_def]
  exact lm1

theorem eval_safe_at {sty: StandardType EC Var Val ValS} (var: Var) (ec: EC) : sty.IsEvalSafe var ec := sty.eval_safe

theorem eval_exists {sty: StandardType EC Var Val ValS} {var: Var} {val: Val} (req: sty.IsValueSafe var val) : ∃(ec: EC), ec var = val := by
  have lm1 := sty.valid.eval_exists var val
  simp [← StandardTypeStruct.isValueSafe_def] at lm1
  exact lm1 req

theorem eval_exists_at {sty: StandardType EC Var Val ValS} (var: Var) (val: Val) (req: sty.IsValueSafe var val) : ∃(ec: EC), ec var = val :=
  sty.eval_exists req

theorem eval_exists_iff {sty: StandardType EC Var Val ValS} {var: Var} {val: Val}
  : (sty.IsValueSafe var val) ↔ (∃(ec: EC), ec var = val) := by
  constructor
  · exact eval_exists
  · rintro ⟨ec, lm1⟩
    rw [Eq.comm] at lm1
    subst lm1
    dsimp [← isEvalSafe_def]
    exact eval_safe

theorem not_mem_iff_forall_eval_ne {sty: StandardType EC Var Val ValS} {var: Var} {val: Val}
  : (val ∉ sty.dom var) ↔ (∀(ec: EC), ec var ≠ val) := by
  rw [← not_iff_not]
  simp
  exact sty.eval_exists_iff


theorem toStruct_injective : Function.Injective (@StandardType.toStruct EC Var Val ValS _ _) := by
  rintro ⟨s1, _⟩
  rintro ⟨s2, _⟩
  simp

@[ext]
theorem eval_ext {sty1 sty2: StandardType EC Var Val ValS} (req: ∀(ec: EC) (var: Var), (sty1.IsEvalSafe var ec) ↔ (sty2.IsEvalSafe var ec)) : sty1 = sty2 := by
  dsimp [isEvalSafe_def] at req
  rw [← toStruct_injective.eq_iff, StandardTypeStruct.value_ext_iff]
  intro var val
  have lm1_1 := sty1.valid.eval_exists var val
  have lm1_2 := sty2.valid.eval_exists var val
  constructor
  · intro lm2
    obtain ⟨ec, lm3⟩ := lm1_1 lm2
    rewrite [Eq.comm] at lm3
    subst lm3
    specialize req ec var
    exact req.mp lm2
  · intro lm2
    obtain ⟨ec, lm3⟩ := lm1_2 lm2
    rewrite [Eq.comm] at lm3
    subst lm3
    specialize req ec var
    exact req.mpr lm2


instance subsingleton : Subsingleton (StandardType EC Var Val ValS) where
  allEq sty1 sty2 := by
    simp only [StandardType.eval_ext_iff]
    intro ec var
    have lm1 := sty1.valid.type_safe ec var
    have lm2 := sty2.valid.type_safe ec var
    dsimp at lm1 lm2
    dsimp [isEvalSafe_def, StandardTypeStruct.isValueSafe_def]
    exact Iff.intro (fun _ => lm2) (fun _ => lm1)



inductive IsEvalSafeSet (sty: StandardType EC Var Val ValS) (ec: EC) : ValS → Prop where
  | intro (var: Var) (req: sty.IsEvalSafe var ec) : IsEvalSafeSet sty ec (sty.dom var)

/-
theorem isEvalSafeSet_iff_eval_safe {sty: StandardType EC Var Val ValS} {ec: EC} {valS: ValS}
  : (IsEvalSafeSet sty ec valS) ↔ (∃(var: Var), (sty.dom var = valS) ∧ sty.IsEvalSafe var ec) := by
  constructor
  · intro lm1
    rcases lm1 with ⟨var, lm1⟩
    exists var
  · rintro ⟨var, lm1, lm2⟩
    rewrite [Eq.comm] at lm1
    subst lm1
    exact .intro var lm2
-/



/-
def IsSafe (sty: StandardType EC Var Val) (v: Var) (D: Set Val) : Prop := D ⊆ sty.dom v


theorem isSafe_iff {sty: StandardType EC Var Val} {var: Var} {D: Set Val}
  : IsSafe sty var D ↔ (∀(val: Val), (val ∈ D) → (val ∈ sty.dom var)) := by
  simp [IsSafe, Set.subset_def]

abbrev DecidableSafe (sty: StandardType EC Var Val) (ValS: Type*) [SetLike ValS Val] : Type _ := (v: Var) → (vals: ValS) → Decidable (sty.IsSafe v vals)

namespace DecidableSafe

@[reducible]
def of_iff {sty: StandardType EC Var Val} (ValS: Type*) [SetLike ValS Val] (dec: ∀(var: Var) (vals: ValS), Decidable (∀ (val: Val), ((val ∈ vals) → (val ∈ sty.dom var))))
  : sty.DecidableSafe ValS :=
  fun _ _ => decidable_of_iff' _ sty.isSafe_iff

end DecidableSafe
-/

@[ext (flat := false)]
structure ValueSetSafeDecidableStruct (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val]
  extends toBase: StandardTypeStruct Var Val ValS where
  isValueSetSafe: Var → ValS → Bool
  --dom : Var → Set Val
  --isSafe : Var → ValI → Bool

structure IsValueSetSafeDecidable {EC Var Val ValS: Type*} [EvalLike EC Var Val] [SetLike ValS Val] (s: ValueSetSafeDecidableStruct EC Var Val ValS) : Prop
  extends toBase: IsStandardType (SetLike.coe ∘ s.dom) EC where
  isValueSetSafe_valid (var: Var) (valS: ValS) : ((s.isValueSetSafe var valS) = .true) ↔ (s.IsValueSetSafe var valS)

structure ValueSetSafeDecidable (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val]
  extends toStruct: ValueSetSafeDecidableStruct EC Var Val ValS where
  valid: IsValueSetSafeDecidable toStruct

namespace IsValueSetSafeDecidable

variable {EC Var Val ValS: Type*} [EvalLike EC Var Val] [SetLike ValS Val] {s: ValueSetSafeDecidableStruct EC Var Val ValS}

def toStandardType (h: IsValueSetSafeDecidable s) : StandardType EC Var Val ValS := ⟨s.toBase, h.toBase⟩

theorem toStandardType_congr {s1 s2: ValueSetSafeDecidableStruct EC Var Val ValS} {h1: IsValueSetSafeDecidable s1} {h2: IsValueSetSafeDecidable s2}
  (req: h1.toStandardType = h2.toStandardType)
  : s1 = s2 := by
  rewrite [StandardType.eval_ext_iff] at req
  rcases h1 with ⟨lm1_1, lm2_1⟩
  rcases h2 with ⟨lm1_2, lm2_2⟩
  dsimp [toStandardType, StandardType.isEvalSafe_def] at req
  rw [ValueSetSafeDecidableStruct.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [StandardTypeStruct.value_valueSet_ext_iff]
    intro var valS val lm3
    have lm4_1 := lm1_1.eval_exists
    have lm4_2 := lm1_2.eval_exists
    simp [← StandardTypeStruct.isValueSafe_def] at lm4_1 lm4_2
    specialize lm4_1 var val
    specialize lm4_2 var val
    constructor
    · intro lm5
      obtain ⟨ec, lm6⟩ := lm4_1 lm5
      rewrite [Eq.comm] at lm6
      subst lm6
      specialize req ec var
      exact req.mp lm5
    · intro lm5
      obtain ⟨ec, lm6⟩ := lm4_2 lm5
      rewrite [Eq.comm] at lm6
      subst lm6
      specialize req ec var
      exact req.mpr lm5
  · simp only [funext_iff]
    intro var valS
    specialize lm2_1 var valS
    specialize lm2_2 var valS
    have lm4_1 := lm1_1.eval_exists
    have lm4_2 := lm1_2.eval_exists
    simp [← StandardTypeStruct.isValueSafe_def] at lm4_1 lm4_2
    specialize lm4_1 var
    specialize lm4_2 var
    dsimp [StandardTypeStruct.isValueSetSafe_eq_isValueSafe] at lm2_1 lm2_2
    replace req := fun ec => req ec var
    by_contra lm3
    rcases lm5: s1.isValueSetSafe var valS
    · simp [lm5] at lm3
      simp [lm3] at lm2_2
      simp [lm5] at lm2_1
      rcases lm2_1 with ⟨val, lm6, lm7⟩
      specialize lm2_2 val lm6
      specialize lm4_2 val lm2_2
      obtain ⟨ec, lm4_2⟩ := lm4_2
      rewrite [Eq.comm] at lm4_2
      subst lm4_2
      specialize req ec
      simp [lm2_2, lm7] at req
    · simp [lm5] at lm3
      simp [lm3] at lm2_2
      simp [lm5] at lm2_1
      rcases lm2_2 with ⟨val, lm6, lm7⟩
      specialize lm2_1 val lm6
      specialize lm4_1 val lm2_1
      obtain ⟨ec, lm4_1⟩ := lm4_1
      rewrite [Eq.comm] at lm4_1
      subst lm4_1
      specialize req ec
      simp [lm2_1, lm7] at req

theorem toStandardType_congr_iff {s1 s2: ValueSetSafeDecidableStruct EC Var Val ValS} (req1: IsValueSetSafeDecidable s1) (req2: IsValueSetSafeDecidable s2)
  : (s1 = s2) ↔ (req1.toStandardType = req2.toStandardType) := by
  constructor
  · intro lm1; subst lm1; rfl
  · exact toStandardType_congr

--instance {h: IsValueSetSafeDecidable s} {var: Var} {valS: ValS} : Decidable (s.IsValueSetSafe var valS) :=
--  decidable_of_iff (s.isValueSetSafe var valS = .true) (by simp)

end IsValueSetSafeDecidable

namespace ValueSetSafeDecidable

variable {EC Var Val ValS: Type*} [EvalLike EC Var Val] [SetLike ValS Val]

def toStandardType (v: ValueSetSafeDecidable EC Var Val ValS) : StandardType EC Var Val ValS := v.valid.toStandardType

theorem toStandardType_injective : Function.Injective (toStandardType: ValueSetSafeDecidable EC Var Val ValS → StandardType EC Var Val ValS) := by
  rintro ⟨s1, lm1⟩ ⟨s2, lm2⟩
  simp [toStandardType]
  exact IsValueSetSafeDecidable.toStandardType_congr


instance subsingleton : Subsingleton (ValueSetSafeDecidable EC Var Val ValS) where
  allEq v1 v2 := by
    rw [← toStandardType_injective.eq_iff]
    exact Subsingleton.elim _ _

instance decidableValueSetSafe {s: ValueSetSafeDecidable EC Var Val ValS} {var: Var} {valS: ValS} : Decidable (s.IsValueSetSafe var valS) :=
  decidable_of_iff (s.isValueSetSafe var valS) (s.valid.isValueSetSafe_valid var valS)


end ValueSetSafeDecidable

def TmpeType : Type _ := Type → ((Type → Type) → (Type → Type)) → Type → Type

class HasSafeDecidable (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] where
  standardType : StandardType.ValueSetSafeDecidable EC Var Val ValS
  decidableMem (valS: ValS) : DecidablePred (· ∈ valS)

attribute [reducible, instance] HasSafeDecidable.decidableMem

namespace HasSafeDecidable

instance subsingleton : Subsingleton (HasSafeDecidable EC Var Val ValS) where
  allEq := by
    rintro ⟨s1, d1⟩ ⟨s2, d2⟩
    congr
    · exact Subsingleton.elim _ _
    · exact Pi.instSubsingleton.elim _ _

abbrev standardTypeAt (EC ValS: Type*) {Var Val: Type*} [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] : StandardType.ValueSetSafeDecidable EC Var Val ValS :=
  HasSafeDecidable.standardType

variable [HasSafeDecidable EC Var Val ValS]

instance toUniqueValueSetSafeDecidable : Unique (StandardType.ValueSetSafeDecidable EC Var Val ValS) where
  default := standardType
  uniq x := Subsingleton.elim x _

instance toUniqueStandardType : Unique (StandardType EC Var Val ValS) where
  default := standardType.toStandardType
  uniq x := Subsingleton.elim x _

@[defeq]
theorem standardTypeAt_def : standardTypeAt EC ValS = standardType := rfl

@[defeq]
theorem standardTypeAt_eq_default : standardTypeAt EC ValS = default := rfl

@[defeq]
theorem standardTypeAt_toStandardType_eq_default : (standardTypeAt EC ValS).toStandardType = default := rfl

@[defeq]
theorem standardTypeAt_toStruct_toBase_eq_toStandardType_toStruct : (standardTypeAt EC ValS).toStruct.toBase = (standardTypeAt EC ValS).toStandardType.toStruct := rfl

section SynthExample

set_option trace.Meta.synthInstance true

example {var: Var} {valS: ValS} : Decidable ((standardTypeAt EC ValS).IsValueSetSafe var valS) := inferInstance

example {valS: ValS} : DecidablePred (· ∈ valS) := inferInstance

--example {var: Var} {val: Val} : Decidable ((standardTypeAt EC ValS).IsValueSafe var val) := inferInstance

end SynthExample


instance decidalbeValueSafe {var: Var} {val: Val} : Decidable ((HasSafeDecidable.standardType: StandardType.ValueSetSafeDecidable EC Var Val ValS).IsValueSafe var val) :=
  decidable_of_iff (val ∈ (standardTypeAt EC ValS).dom var) (by dsimp [StandardTypeStruct.isValueSafe_def]; rfl)



end HasSafeDecidable

@[ext]
structure AtomicPropStruct (Var ValS: Type*) where
  var: Var
  spec: ValS

namespace AtomicPropStruct

--variable [HasSafeDecidable EC Var Val ValS]

def IsEvalSpecSafe (s: AtomicPropStruct Var ValS) (ec: EC) : Prop := (ec s.var) ∈ s.spec

@[defeq]
theorem isEvalSpecSafe_def {s: AtomicPropStruct Var ValS} {ec: EC} : s.IsEvalSpecSafe ec = ((ec s.var) ∈ s.spec) := rfl


instance decidableEvalSpecSafe {s: AtomicPropStruct Var ValS} {ec: EC} [DecidablePred (· ∈ s.spec)] : Decidable (s.IsEvalSpecSafe ec) :=
  inferInstanceAs (Decidable ((ec s.var) ∈ s.spec))


def decideEvalSpecSafe (s: AtomicPropStruct Var ValS) [DecidablePred (· ∈ s.spec)] (ec: EC) : Bool := decide (s.IsEvalSpecSafe ec)

@[defeq]
theorem decideEvalSpecSafe_def {s: AtomicPropStruct Var ValS} [DecidablePred (· ∈ s.spec)] {ec: EC}
  : s.decideEvalSpecSafe ec = decide (s.IsEvalSpecSafe ec) :=
  rfl

def equivOfToProd : (AtomicPropStruct Var ValS) ≃ (Var × ValS) where
  toFun s := (s.var, s.spec)
  invFun prod := ⟨prod.fst, prod.snd⟩

instance toFintype [Fintype Var] [Fintype ValS] : Fintype (AtomicPropStruct Var ValS) := Fintype.ofEquiv _ equivOfToProd.symm

/-
structure AreValueSetEquiv (f: Var → ValS) (s1 s2: AtomicPropStruct Var ValS) : Prop where
  var_equiv: f s1.var = f s2.var
  spec_eq: s1.spec = s2.spec

theorem areValueSetEquiv_iff {f: Var → ValS} {s1 s2: AtomicPropStruct Var ValS}
  : (AreValueSetEquiv f s1 s2) ↔ ((f s1.var = f s2.var) ∧ (s1.spec = s2.spec)) := by
  constructor
  · rintro ⟨lm1, lm2⟩
    exact ⟨lm1, lm2⟩
  · rintro ⟨lm1, lm2⟩
    exact ⟨lm1, lm2⟩


namespace AreValueSetEquiv

theorem equivalence_of (f: Var → ValS) : Equivalence (AreValueSetEquiv f) where
  refl s := by refine .mk ?_ ?_ <;> rfl
  symm := by
    intro s1 s2
    rintro ⟨lm1, lm2⟩
    exact .mk lm1.symm lm2.symm
  trans := by
    intro s1 s2 s3
    rintro ⟨lm1_1, lm2_1⟩ ⟨lm1_2, lm2_2⟩
    refine .mk ?_ ?_
    · exact lm1_1.trans lm1_2
    · exact lm2_1.trans lm2_2

instance is_equiv_of (f: Var → ValS) : IsEquiv (AtomicPropStruct Var ValS) (AreValueSetEquiv f) := .of_equivalence (equivalence_of f)

@[reducible]
def setoidOf (f: Var → ValS) : Setoid (AtomicPropStruct Var ValS) where
  r := AreValueSetEquiv f
  iseqv := equivalence_of f

end AreValueSetEquiv
-/

end AtomicPropStruct

structure IsAtomicProp {Var ValS: Type*} (s: AtomicPropStruct Var ValS) (EC Val: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] : Prop where
 spec_safe: (HasSafeDecidable.standardTypeAt EC ValS).IsValueSetSafe s.var s.spec

theorem isAtomicProp_iff {Var ValS: Type*} {s: AtomicPropStruct Var ValS} {EC Val: Type*} [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS]
  : IsAtomicProp s EC Val ↔ (HasSafeDecidable.standardTypeAt EC ValS).IsValueSetSafe s.var s.spec := by
  constructor
  · rintro ⟨lm1⟩; exact lm1
  · intro lm1; exact .mk lm1

section IsAtomicPropLemmas

open HasSafeDecidable

variable [HasSafeDecidable EC Var Val ValS] {s: AtomicPropStruct Var ValS}

namespace IsAtomicProp


instance decidable (s: AtomicPropStruct Var ValS) : Decidable (IsAtomicProp s EC Val) := decidable_of_iff' _ isAtomicProp_iff

theorem value_safe_of_spec_elem (h: IsAtomicProp s EC Val) (val: ↑(s.spec)) : (standardTypeAt EC ValS).IsValueSafe s.var val.val := by
  revert val
  simp only [Subtype.forall]
  have lm1 := h.spec_safe
  dsimp [StandardTypeStruct.isValueSetSafe_eq_isValueSafe] at lm1
  exact lm1

theorem spec_subset (h: IsAtomicProp s EC Val) : (s.spec: Set Val) ⊆ (standardTypeAt EC ValS).dom s.var := by
  have lm1 := h.spec_safe
  dsimp [StandardTypeStruct.isValueSetSafe_def] at lm1
  exact lm1

theorem eval_exists_of_spec_elem (h: IsAtomicProp s EC Val) {val: Val} : (val ∈ s.spec) → (∃(ec: EC), ec s.var = val) := by
  have lm1 := h.value_safe_of_spec_elem
  simp only [Subtype.forall] at lm1
  specialize lm1 val
  intro lm2
  specialize lm1 lm2
  dsimp [standardTypeAt_toStruct_toBase_eq_toStandardType_toStruct] at lm1
  rewrite [StandardType.eval_exists_iff] at lm1
  exact lm1
    --let sty := (standardTypeAt EC ValS).toStandardType
    --simp [(standardTypeAt EC ValS).toStandardType.eval_exists_iff] at lm1

end IsAtomicProp

theorem isAtomicProp_iff_forall_spec_elem_value_safe : (IsAtomicProp s EC Val) ↔ (∀(val: ↑(s.spec)), (standardTypeAt EC ValS).IsValueSafe s.var val.val) := by
  constructor
  · exact IsAtomicProp.value_safe_of_spec_elem
  · intro lm1
    rw [isAtomicProp_iff]
    rewrite [Subtype.forall] at lm1
    dsimp [StandardTypeStruct.isValueSetSafe_eq_isValueSafe]
    exact lm1

theorem isAtomicProp_iff_spec_subset : (IsAtomicProp s EC Val) ↔ ((s.spec: Set Val) ⊆ (standardTypeAt EC ValS).dom s.var) := by
  constructor
  · exact IsAtomicProp.spec_subset
  · intro lm1
    refine .mk ?_
    dsimp [StandardTypeStruct.isValueSetSafe_def]
    exact lm1


end IsAtomicPropLemmas

@[ext]
structure AtomicProp (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS]
  extends toStruct: AtomicPropStruct Var ValS where
  valid: IsAtomicProp toStruct EC Val


namespace AtomicProp

open HasSafeDecidable

variable [HasSafeDecidable EC Var Val ValS]

structure SingletonOPStruct (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] where
  op (var: Var) (val: Val) (req: (standardTypeAt EC ValS).IsValueSafe var val) : AtomicProp EC Var Val ValS


structure IsSingletonOP (s: SingletonOPStruct EC Var Val ValS) : Prop where
  var_eq (var: Var) (val: Val) (req: (standardTypeAt EC ValS).IsValueSafe var val) : (s.op var val req).var = var
  spec_eq_singleton (var: Var) (val: Val) (req: (standardTypeAt EC ValS).IsValueSafe var val) : ((s.op var val req).spec: Set Val) = {val}

@[ext]
structure SingletonOP (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS]
  extends toStruct: SingletonOPStruct EC Var Val ValS where
  valid: IsSingletonOP toStruct

namespace SingletonOP

instance subsingleton : Subsingleton (SingletonOP EC Var Val ValS) where
  allEq sop1 sop2 := by
    simp only [SingletonOP.ext_iff, funext_iff]
    intro var val lm1
    obtain ⟨lm1_1, lm2_1⟩ := sop1.valid
    obtain ⟨lm1_2, lm2_2⟩ := sop2.valid
    specialize lm1_1 var val lm1
    specialize lm2_1 var val lm1
    specialize lm1_2 var val lm1
    specialize lm2_2 var val lm1
    let (eq := lm3_1) ap1 := sop1.op var val lm1
    let (eq := lm3_2) ap2 := sop2.op var val lm1
    simp [← lm3_1, ← lm3_2] at ⊢ lm1_1 lm2_1 lm1_2 lm2_2
    simp [AtomicProp.ext_iff]
    rw [lm1_1, lm1_2]
    simp only [true_and]
    have lm4 := lm2_1.trans lm2_2.symm
    simpa using lm4

end SingletonOP

class HasSingletonOP (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] where
  singletonOP: SingletonOP EC Var Val ValS

namespace HasSingletonOP

instance subsingleton : Subsingleton (HasSingletonOP EC Var Val ValS) where
  allEq := by
    rintro ⟨_⟩ ⟨_⟩
    congr
    exact Subsingleton.elim _ _

end HasSingletonOP


def equivOfToSubtype : AtomicProp EC Var Val ValS ≃ { toStruct: AtomicPropStruct Var ValS // IsAtomicProp toStruct EC Val } where
  toFun x := ⟨x.toStruct, x.valid⟩
  invFun x := ⟨x.val, x.property⟩

instance toFintype [Fintype Var] [Fintype ValS] : Fintype (AtomicProp EC Var Val ValS) := Fintype.ofEquiv _ equivOfToSubtype.symm


instance decidableEvalSpecSafe {ap: AtomicProp EC Var Val ValS} {ec: EC} : Decidable (ap.IsEvalSpecSafe ec) :=
  ap.toStruct.decidableEvalSpecSafe


instance {ap: AtomicProp EC Var Val ValS} : DecidablePred (· ∈ ap.spec) := HasSafeDecidable.decidableMem EC Var ap.spec

@[defeq]
theorem decideEvalSpecSafe_eq_decide {ap: AtomicProp EC Var Val ValS} {ec: EC}
  : ap.decideEvalSpecSafe ec = decide (ap.IsEvalSpecSafe ec) :=
  rfl

/-
@[reducible]
def setoidOf (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] : Setoid (AtomicProp EC Var Val ValS) :=
  (AtomicPropStruct.AreValueSetEquiv.setoidOf (HasSafeDecidable.standardTypeAt EC ValS).dom).comap AtomicProp.toStruct

def AreValueSetEquiv (ap1 ap2: AtomicProp EC Var Val ValS) : Prop := (setoidOf EC Var Val ValS).r ap1 ap2

theorem areValueSetEquiv_iff {ap1 ap2: AtomicProp EC Var Val ValS}
  : AreValueSetEquiv ap1 ap2 ↔ AtomicPropStruct.AreValueSetEquiv (HasSafeDecidable.standardTypeAt EC ValS).dom ap1.toStruct ap2.toStruct := by
  dsimp [AreValueSetEquiv]
  rw [Setoid.comap_rel]
  dsimp [Setoid.r]
  rfl

def SetEmbeddable (EC Var Val ValS: Type*) [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] : Type _ :=
  Quotient (setoidOf EC Var Val ValS)

def toSetEmbeddable (ap: AtomicProp EC Var Val ValS) : SetEmbeddable EC Var Val ValS := Quotient.mk _ ap
-/

theorem decideEvalSpecSafe_injective (sop: SingletonOP EC Var Val ValS) : Function.Injective (fun (ec: EC) (ap: AtomicProp EC Var Val ValS) => ap.decideEvalSpecSafe ec) := by
  intro ec1 ec2 lm1
  simp [funext_iff, decideEvalSpecSafe_eq_decide] at lm1
  simp only [DFunLike.ext_iff]
  intro var
  have lm2 := (standardTypeAt EC ValS).toStandardType.eval_safe_at var ec1
  dsimp [← standardTypeAt_toStruct_toBase_eq_toStandardType_toStruct, isEvalSafe_def] at lm2
  let sgtAp := sop.op var (ec1 var) lm2
  specialize lm1 sgtAp
  dsimp [AtomicPropStruct.isEvalSpecSafe_def] at lm1
  subst sgtAp
  have lm3 := sop.valid.spec_eq_singleton var (ec1 var) lm2
  simp [← SetLike.mem_coe, lm3] at lm1
  have lm4 := sop.valid.var_eq var (ec1 var) lm2
  simp [lm4] at lm1
  exact lm1.symm



theorem spec_eq_of_var_eq_and_forall_isEvalSpecSafe_iff
  {ap1 ap2: AtomicProp EC Var Val ValS} (req1: ap1.var = ap2.var) (req2: ∀(ec: EC), ap1.IsEvalSpecSafe ec ↔ ap2.IsEvalSpecSafe ec)
  : ap1.spec = ap2.spec := by
  dsimp [AtomicPropStruct.isEvalSpecSafe_def] at req2
  simp only [SetLike.ext_iff]
  let (eq := lm1) sty := HasSafeDecidable.standardTypeAt EC ValS
  rcases ap1 with ⟨s1, ⟨lm2_1⟩⟩
  rcases ap2 with ⟨s2, ⟨lm2_2⟩⟩
  simp at req1 req2 ⊢
  intro val
  simp [← lm1] at lm2_1 lm2_2
  dsimp [StandardTypeStruct.isValueSetSafe_eq_isValueSafe] at lm2_1 lm2_2
  specialize lm2_1 val
  specialize lm2_2 val
  have lm3 := sty.valid.eval_exists
  simp [← StandardTypeStruct.isValueSafe_def] at lm3
  have lm3_1 := lm3 s1.var val
  have lm3_2 := lm3 s2.var val
  clear lm3
  constructor
  · intro lm4
    specialize lm2_1 lm4
    specialize lm3_1 lm2_1
    obtain ⟨ec, lm3_1⟩ := lm3_1
    rewrite [Eq.comm] at lm3_1; subst lm3_1
    specialize req2 ec
    rw [req1]
    exact req2.mp lm4
  · intro lm4
    specialize lm2_2 lm4
    specialize lm3_2 lm2_2
    obtain ⟨ec, lm3_2⟩ := lm3_2
    rewrite [Eq.comm] at lm3_2; subst lm3_2
    specialize req2 ec
    rw [← req1]
    exact req2.mpr lm4

theorem forall_isEvalSpecSafe_iff_iff_spec_eq_of_var_eq {ap1 ap2: AtomicProp EC Var Val ValS} (req: ap1.var = ap2.var)
  : (∀(ec: EC), ap1.IsEvalSpecSafe ec ↔ ap2.IsEvalSpecSafe ec) ↔ (ap1.spec = ap2.spec) := by
  constructor
  · exact spec_eq_of_var_eq_and_forall_isEvalSpecSafe_iff req
  · intro lm1 ec
    rw [SetLike.ext_iff] at lm1
    dsimp [AtomicPropStruct.isEvalSpecSafe_def]
    have lm2 := lm1 (ec ap2.var)
    conv at lm2 => lhs; rw [← req]
    exact lm2




@[reducible]
def toIndicatorLike (EC Var Val ValS: Type*)
  [EvalLike EC Var Val] [SetLike ValS Val] [HasSafeDecidable EC Var Val ValS] [HasSingletonOP EC Var Val ValS] [Fintype Var] [Fintype ValS]
  : PropositionalLogics.EvalLike EC (AtomicProp EC Var Val ValS) where
  coe ec := (fun (ap: AtomicProp EC Var Val ValS) => ap.decideEvalSpecSafe ec ) |> .mk
  coe_injective := by
    intro ec1 ec2
    simp
    have lm1 := AtomicProp.decideEvalSpecSafe_injective (HasSingletonOP.singletonOP: SingletonOP EC Var Val ValS)
    specialize @lm1 ec1 ec2
    dsimp at lm1
    exact lm1


end AtomicProp


class HasProposition.{u1, u2, u3, u4} (EC: Type u1) (Var: Type u2) (Val: Type u3) [EvalLike EC Var Val] where
  ValS: Type u4
  setLike: SetLike ValS Val
  hasSafeDecidable: HasSafeDecidable EC Var Val ValS
  hasSingletonOP: AtomicProp.HasSingletonOP EC Var Val ValS
  fintypeVar: Fintype Var
  fintypeSpec: Fintype ValS

attribute [reducible, instance] HasProposition.setLike HasProposition.hasSafeDecidable HasProposition.hasSingletonOP HasProposition.fintypeVar HasProposition.fintypeSpec

namespace HasProposition

abbrev AtomicPropType (EC Var Val: Type*) [EvalLike EC Var Val] [HasProposition EC Var Val] : Type _ := AtomicProp EC Var Val (HasProposition.ValS EC Var Val)

variable [HasProposition EC Var Val]

instance toIndicatorLike : PropositionalLogics.EvalLike EC (AtomicPropType EC Var Val) := AtomicProp.toIndicatorLike EC Var Val (HasProposition.ValS EC Var Val)

end HasProposition


section Cond

open PropositionalLogics

open HasProposition

inductive IsCond (EC Var Val: Type*) [EvalLike EC Var Val] [HasProposition EC Var Val] : Formula (AtomicPropType EC Var Val) → Prop where
  | nil : IsCond EC Var Val (.true)
  | cons (ap: AtomicPropType EC Var Val) (fml: Formula (AtomicPropType EC Var Val)) (req: IsCond EC Var Val fml) : IsCond EC Var Val (Formula.and (.atom ap) fml)

attribute [simp] IsCond.nil

variable [HasProposition EC Var Val]

namespace IsCond

@[simp]
theorem and_iff {ap: AtomicPropType EC Var Val} {fml: Formula (AtomicPropType EC Var Val)}
  : IsCond EC Var Val (Formula.and (.atom ap) fml) ↔ IsCond EC Var Val fml := by
  constructor
  · intro lm1
    cases lm1
    assumption
  · intro lm1
    exact .cons ap fml lm1

theorem of_atomTuple {as: List (AtomicPropType EC Var Val)} : IsCond EC Var Val (Formula.atomTuple as) := by
  rcases as with _ | ⟨hd, tl⟩
  · dsimp [Formula.atomTuple, Formula.iterAnd]
    exact .nil
  · dsimp [Formula.atomTuple, Formula.iterAnd]
    refine .cons _ _ ?_
    have lm1 := @of_atomTuple tl
    dsimp [Formula.atomTuple] at lm1
    exact lm1

end IsCond


theorem isCond_iff_exists_atomTuple {fml: Formula (AtomicPropType EC Var Val)}
  : IsCond EC Var Val fml ↔ ∃as, Formula.atomTuple as = fml := by
  constructor
  · intro lm1
    induction lm1
    · exists []
    · rename_i ap fml req lm1
      obtain ⟨as, lm1⟩ := lm1
      exists (ap :: as)
      dsimp [Formula.atomTuple] at lm1 ⊢
      dsimp [Formula.iterAnd]
      simpa using lm1
  · rintro ⟨as, lm1⟩
    rw [lm1.symm]
    exact IsCond.of_atomTuple


end Cond

end StandardType


open PropositionalLogics StandardType HasProposition in
@[ext]
structure Cond (EC Var Val: Type*) [EvalLike EC Var Val] [HasProposition EC Var Val] where
  formula: Formula (AtomicPropType EC Var Val)
  valid : IsCond EC Var Val formula

namespace Cond

open PropositionalLogics StandardType.HasProposition

variable {EC Var Val: Type*} [EvalLike EC Var Val] [StandardType.HasProposition EC Var Val]


def ofAtoms (as: List (AtomicPropType EC Var Val)) : Cond EC Var Val where
  formula := Formula.atomTuple as
  valid := StandardType.IsCond.of_atomTuple

def ofAtomsRec (as: List (AtomicPropType EC Var Val)) : Cond EC Var Val :=
  match as with
  | [] => ⟨.true, StandardType.IsCond.nil⟩
  | a :: as => ⟨Formula.and (.atom a) ((ofAtomsRec as).formula), StandardType.IsCond.and_iff.mpr (ofAtomsRec as).valid⟩

theorem ofAtoms_eq_ofAtomsRec_at (as: List (AtomicPropType EC Var Val)) : ofAtoms as = ofAtomsRec as := by
  rcases as with _ | ⟨a, as⟩
  · dsimp [ofAtoms, ofAtomsRec, Formula.atomTuple, Formula.iterAnd]
  · dsimp [ofAtoms, ofAtomsRec, Formula.atomTuple, Formula.iterAnd]
    simp
    have lm1 := ofAtoms_eq_ofAtomsRec_at as
    dsimp [ofAtoms, Formula.atomTuple, Formula.iterAnd] at lm1
    rw [← lm1]

theorem ofAtoms_eq_ofAtomsRec : @ofAtoms = @ofAtomsRec := by
  simp only [funext_iff]
  intro _ _ _ _ _
  exact ofAtoms_eq_ofAtomsRec_at

--(req: ofAtoms as1 = ofAtoms as2) as1 = as2 {as1 as2: List (AtomicPropType EC Var Val)}
theorem ofAtoms_injective : Function.Injective (ofAtoms: List (AtomicPropType EC Var Val) → Cond EC Var Val) := by
  intro as1 as2 req
  simp only [ofAtoms_eq_ofAtomsRec] at req
  rcases as1 with _ | ⟨a1, as1⟩
  <;> rcases as2 with _ | ⟨a2, as2⟩
  <;> simp [ofAtomsRec] at req
  · rfl
  · rcases req with ⟨lm1, lm2⟩
    simp [lm1]
    refine ofAtoms_injective ?_
    simp only [ofAtoms_eq_ofAtomsRec]
    exact Cond.ext lm2

def nil : Cond EC Var Val := ⟨.true, .nil⟩

def cons (ap: AtomicPropType EC Var Val) (cond: Cond EC Var Val) : Cond EC Var Val where
  formula := (Formula.and (.atom ap) cond.formula)
  valid := StandardType.IsCond.and_iff.mpr cond.valid

open StandardType in
@[elab_as_elim]
def recNilCons.{u}
  {motive: (Cond EC Var Val) → Sort u}
  (nil: motive Cond.nil)
  (cons: (ap: AtomicPropType EC Var Val) → (cond: Cond EC Var Val) → motive (Cond.cons ap cond))
  (t: Cond EC Var Val)
  : motive t :=
  match lm1: t.formula  with
  | .true =>
    have lm2: Cond.nil = t := by rcases t with ⟨fml, lm2⟩; simp at ⊢ lm1; subst lm1; dsimp [Cond.nil]
    nil |> lm2.ndrec
  | .and fml1 fml2 =>
    match fml1 with
    | .atom ap =>
      have lm2 : IsCond EC Var Val fml2 := IsCond.and_iff.mp (lm1.ndrec t.valid)
      let cond : Cond EC Var Val := ⟨fml2, lm2⟩
      have lm3 : Cond.cons ap cond = t := by
        subst cond
        dsimp [Cond.cons]
        congr
        exact lm1.symm
      cons ap cond |> lm3.ndrec
    | .and _ _ | .neg _ | .true => absurd t.valid (by intro lm2; rewrite [lm1] at lm2; rcases lm2)
  | .neg _ | .atom _ => absurd t.valid (by intro lm2; rewrite [lm1] at lm2; rcases lm2)

@[defeq]
theorem recNilCons_nil {m n c} : (Cond.nil: Cond EC Var Val).recNilCons (motive := m) n c = n := by
  dsimp [Cond.nil, recNilCons]

@[defeq]
theorem recNilCons_cons {m n c} {ap: AtomicPropType EC Var Val} {cond: Cond EC Var Val}
  : (Cond.cons ap cond).recNilCons (motive := m) n c = c ap cond := by
  dsimp [Cond.cons, recNilCons]


theorem size_lt_size_cons {ap: AtomicPropType EC Var Val} {cond: Cond EC Var Val} : sizeOf cond < sizeOf (cons ap cond) := by
  dsimp [Cond.cons]
  simp
  rcases cond with ⟨fml, _⟩
  simp
  calc
    0 < 1 := zero_lt_one
    _ ≤ _ := Nat.le_add_right _ _


set_option linter.unusedVariables false in
def toAtoms (cond: Cond EC Var Val) : List (AtomicPropType EC Var Val) :=
  cond.recNilCons (motive := fun x => (x = cond) → List (AtomicPropType EC Var Val)) (fun _ => []) (fun ap cond0 lm1 => ap :: cond0.toAtoms) <| rfl
  decreasing_by
    rewrite [Eq.comm] at lm1
    subst lm1
    exact size_lt_size_cons

theorem ofAtoms_toAtoms_leftInverse : Function.LeftInverse (ofAtoms: List (AtomicPropType EC Var Val) → Cond EC Var Val) toAtoms := by
  intro cond
  rw [ofAtoms_eq_ofAtomsRec]
  cases cond using recNilCons
  · unfold toAtoms
    dsimp [recNilCons_nil]
    unfold ofAtomsRec
    dsimp [Cond.nil]
  · rename_i ap cond
    unfold toAtoms
    dsimp [recNilCons_cons]
    unfold ofAtomsRec
    dsimp [Cond.cons]
    congr
    rw [← ofAtoms_eq_ofAtomsRec]
    exact ofAtoms_toAtoms_leftInverse _
  decreasing_by
    rename_i lm1
    subst lm1
    exact size_lt_size_cons

theorem toAtoms_injective : Function.Injective (toAtoms: Cond EC Var Val → List (AtomicPropType EC Var Val)) := ofAtoms_toAtoms_leftInverse.injective


end Cond


class CondLike (CC EC Var Val: Type*) [EvalLike EC Var Val] [StandardType.HasProposition EC Var Val] where
  toCond: CC → Cond EC Var Val
  toCond_Injective: Function.Injective toCond


namespace CondLike

open PropositionalLogics StandardType.HasProposition

variable {CC EC Var Val: Type*} [EvalLike EC Var Val] [StandardType.HasProposition EC Var Val] [CondLike CC EC Var Val]

def toFormula (cond: CC) : Formula (AtomicPropType EC Var Val) := (CondLike.toCond cond).formula


end CondLike



end ProgramGraph

/-!

### Definition 2.13. Program Graph (PG)

-/


open ProgramGraph in
structure ProgramGraph.{u1, u2, u3, u4, u5, u6} (CC: Type u1) (EC: Type u2) (Var: Type u3) (Val: Type u4) [EvalLike EC Var Val] [StandardType.HasProposition EC Var Val] [CondLike CC EC Var Val] where
  Loc: Type u5
  [decidableEqOfLoc: DecidableEq Loc]
  Act: Type u6
  effect: Act → EC → EC
  ctr: Loc → CC → Act → Loc → Prop
  loc0: Loc → Prop
  g0: Cond EC Var Val


/-!

### Definition 2.15. Transition System Semantics of a Program Graph

-/

namespace ProgramGraph

variable {CC EC Var Val: Type*} [EvalLike EC Var Val] [StandardType.HasProposition EC Var Val] [CondLike CC EC Var Val]

instance (pg: ProgramGraph CC EC Var Val) : DecidableEq (pg.Loc) := pg.decidableEqOfLoc

def Loc0 (pg: ProgramGraph CC EC Var Val) : Set (pg.Loc) := { l | pg.loc0 l }



@[mk_iff]
inductive Transition (pg: ProgramGraph CC EC Var Val) : pg.Loc → EC → pg.Act → pg.Loc → EC → Prop where
  | intro (l1 l2: pg.Loc) (g: CC) (act: pg.Act) (η: EC) (req1: pg.ctr l1 g act l2)
          (req2: η ⊨ₚ (CondLike.toFormula g))
      : Transition pg l1 η act l2 (pg.effect act η)

          --(req2: ⟦η⟧ ⊨ₚ⟦ cl.standardType.indicateAtomicProp ⟧ (cl.toCond g).formula)

theorem Transition.of_exists
  {pg: ProgramGraph CC EC Var Val} {l1 l2: pg.Loc} {act: pg.Act} {η: EC}
  (req: ∃(g: CC), (pg.ctr l1 g act l2) ∧ (η ⊨ₚ (CondLike.toFormula g)))
  : pg.Transition l1 η act l2 (pg.effect act η) := by
  rcases req with ⟨g, req1, req2⟩
  exact .intro l1 l2 g act η req1 req2

  --refine .intro l1 l2 g act η ?_ ?_
  --·

open PropositionalLogics StandardType.HasProposition in
def labeling (pg: ProgramGraph CC EC Var Val) (s: pg.Loc × EC) (ap: pg.Loc ⊕ CC) : Bool :=
  let ⟨l, η⟩ := s
  match ap with
  | .inl l2 => decide (l = l2)
  | .inr g => decide (η ⊨ₚ (CondLike.toFormula g)) --(Indicator.mk (η: PropositionalLogics.Eval (AtomicPropType EC Var Val))).evalFormulaToBool (CondLike.toFormula g) --(Indicator.mk (cl.standardType.indicateAtomicProp η)).evalFormulaToBool (cl.toCond g).formula


open PropositionalLogics in
@[reducible]
def toTransitionSystem (pg: ProgramGraph CC EC Var Val) : TransitionSystem where
  S := pg.Loc × EC
  Act := pg.Act
  I := { ⟨l, η⟩ | (l ∈ pg.Loc0) ∧ (η ⊨ₚ pg.g0.formula) }
  AP := pg.Loc ⊕ CC
  tr s1 act s2 := pg.Transition s1.fst s1.snd act s2.fst s2.snd
  L := pg.labeling

/-
open PropositionalLogics in
theorem toTransitionSystem_Injective : Function.Injective (toTransitionSystem: ProgramGraph CC EC Var Val → TransitionSystem) := by
    intro pg1 pg2 lm1
    rcases pg1 with ⟨Loc1, Act, effect1, ctr1, loc01, cond1⟩
    rcases pg2 with ⟨Loc2, Act2, effect2, ctr2, loc02, cond2⟩
    simp at lm1
    rcases lm1 with ⟨lm1, lm2, lm3, lm4, lm5, lm6⟩
    subst lm2
    simp
    by_cases lm7: Loc1 = Loc2
    · subst lm7
      simp only at lm1 lm5; clear lm1 lm5
      have lm8 : Subsingleton (DecidableEq Loc1) := inferInstance
      rename_i deq1 deq2
      replace lm8 := lm8.elim deq1 deq2
      subst lm8
      simp_all
      simp [funext_iff] at lm3 lm6
      simp [Set.ext_iff, SatRel.defaultAt_isSat_iff] at lm4
      dsimp [Loc0] at lm4
      simp [labeling] at lm6; clear lm6
      simp [transition_iff, SatRel.defaultAt_isSat_iff] at lm3
      dsimp [CondLike.toFormula] at lm3
      conv at lm3 => ext; ext; ext; ext; ext; rw [← not_iff_not]
      simp at lm3
      cases cond1 using Cond.recNilCons
      · cases cond2 using Cond.recNilCons
        dsimp [Cond.nil, Indicator.evalFormulaToBool] at lm4
        simp at lm4
        by_cases lm5: Nonempty EC
        · rcases lm5 with ⟨ec⟩
          have lm5 : loc01 = loc02 := by
            simp [funext_iff]
            exact fun x => lm4 x ec
          subst lm5
          simp at lm4 ⊢; clear lm4
-/
          --simp [funext_iff]
/-
          replace lm4 := fun loc => lm4 loc ec
          conv => arg 2; arg 2; arg 1; simp [funext_iff]; rw [eq_true lm4]
          simp
          simp [funext_iff]
-/

/-
      simp [labeling] at lm6; clear lm6
      refine ⟨?_, ?_, ?_⟩
      · simp only [funext_iff]
        intro act ec
        have lm5_1 := fun loc1 loc2 => lm3 loc1 ec act loc2 (effect1 act ec)
        have lm5_2 := fun loc1 loc2 => lm3 loc1 ec act loc2 (effect2 act ec)
        simp [transition_iff, SatRel.defaultAt_isSat_iff] at lm5_1 lm5_2
        conv at lm5_1 => ext; ext; rw [← not_iff_not]
        conv at lm5_2 => ext; ext; rw [← not_iff_not]
        simp at lm5_1 lm5_2
-/
        --rewrite [← not_iff_not] at lm4_1
        --conv at lm4_2 => ext; ext; lhs; arg 1; ext; arg 2; arg 2; rw [Eq.comm]
        --have lm4 := fun loc1 loc2 => Iff.trans (lm4_1 loc1 loc2) (lm4_2 loc1 loc2)


/-
inductive OfLoc.{u1, u2, u3, u4, u5, u6}
  (CC: Type u1) (EC: Type u2) (Var: Type u3) (Val: Type u4) [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] [CondLike CC EC Var Val] : Type u5 → Type _ where
  | mk (pg: ProgramGraph.{u1, u2, u3, u4, u5, u6} CC EC Var Val) : OfLoc CC EC Var Val pg.Loc
-/


namespace OfLoc

/-
universe u1 u2 u3 u4 u5
variable {CC: Type u1} {EC: Type u2} {Var: Type u3} {Val: Type u4} [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] [CondLike CC EC Var Val] {Loc: Type u5}


def toTransitionSystem (pgl: OfLoc CC EC Var Val Loc) : TransitionSystem := pgl.casesOn (fun pg => pg.toTransitionSystem)
-/

/-
instance [h: Nonempty Loc] : TransitionSystemLike (OfLoc CC EC Var Val Loc) where
  coe pgl := pgl.toTransitionSystem
  coe_injective := by
    rintro ⟨pg1⟩
    intro pgl2 lm1
    rcases pg1 with ⟨Loc, Act1, effect1, ctr1, loc01, ⟨fmt1, lm5⟩⟩
    dsimp at pgl2 h
    rcases pgl2 with ⟨pg2⟩
    dsimp [toTransitionSystem] at lm1
    simp [ProgramGraph.toTransitionSystem] at lm1
    rcases lm1 with ⟨lm1, lm2, lm3, lm4⟩
    subst lm1
    simp [funext_iff, labeling] at lm4; clear lm4
    simp [Set.ext_iff, Loc0] at lm3
    simp [funext_iff, transition_iff] at lm2
    congr
    · simp only [funext_iff]
      intro act ec
      obtain ⟨loc⟩ := h
      specialize lm2 loc ec act loc ec
      rewrite [← not_iff_not] at lm2
      simp at lm2
-/
    --rcases g01 with ⟨fml1, lm5⟩
/-
    congr
    · simp [funext_iff, transition_iff] at lm2
      simp only [funext_iff]
      intro act ec
      obtain ⟨loc⟩ := h
-/
/-
      replace lm2 := fun l1 l2 => lm2 l1 ec act l2 ec
      conv at lm2 => ext; ext; rw [← not_iff_not]
      simp at lm2
-/


    --simp [funext_iff, transition_iff, StandardType.indicateAtomicProp] at lm2

    --simp [Set.ext_iff] at lm3
    --simp at lm2 lm3 lm4



    --dsimp [Function.Injective toTransitionSystem]



/-


def toTransitionSystem.{u6} (pgl: OfLoc.{u1, u2, u3, u4, u5, u6} CC EC Var Val Loc) : TransitionSystem := match pgl with | .mk pg => pg.toTransitionSystem



instance toTransitionSystemLike.{u6} : TransitionSystemLike.{_} (OfLoc.{u1, u2, u3, u4, u5, u6} CC EC Var Val Loc) where
  coe pgl := pgl.toTransitionSystem
-/

end OfLoc

/-
instance toTransitionSystemLike {Loc} : TransitionSystemLike (OfLoc CC EC Var Val Loc) where
  coe := fun ⟨pg⟩ => pg.toTransitionSystem
  coe_injective := by
-/

/-
abbrev KernelQuotient (CC EC Var Val: Type*) [EvalLike EC Var Val] [Fintype Var] [Fintype Val] [DecidableEq Val] [CondLike CC EC Var Val] : Type _ := Quotient (Setoid.ker (toTransitionSystem : ProgramGraph CC EC Var Val → TransitionSystem))

def toKernelQuotient (pg: ProgramGraph CC EC Var Val) : KernelQuotient CC EC Var Val :=
  Quotient.mk (Setoid.ker toTransitionSystem) pg


instance : TransitionSystemLike (KernelQuotient CC EC Var Val)
-/

/-
open PropositionalLogics in
theorem toTransitionSystem_Injective : Function.Injective (@toTransitionSystem CC EC Var Val Loc _ _ _ _ _ _) := by
  rintro ⟨A1, ef1, ctr1, loc01, g01⟩ ⟨A2, ef2, ctr2, loc02, g02⟩
  simp [toTransitionSystem]
  intro lm1 lm2 lm3
  subst lm1
  simp at lm2 ⊢
  simp [funext_iff, transition_iff] at lm2
  simp [Set.ext_iff, ProgramGraph.Loc0, SatRel.IsSat, SatRel.defaultAt, Inhabited.default,
        DFunLike.coe, SatRel.default, EvalLike.AreEvalToTrueAt, EvalLike.toIndicator,
        ← Indicator.AreEvalToTrue.eq_true_iff] at lm3 lm2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [funext_iff]
    intro act ec
-/


end ProgramGraph


end Nemonuri

end
