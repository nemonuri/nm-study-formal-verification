module


public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Setoid.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import Nemonuri.PropositionalLogics


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1 Transition Systems, p.19

-/

@[expose] public section

namespace Nemonuri

open PropositionalLogics Formula


structure TransitionSystem.{u1, u2, u3} where
  /-- A set of states -/
  S: Type u1
  /-- A set of actions -/
  Act: Type u2
  /-- A transition relation -/
  tr: S → Act → S → Prop
  /-- a set of initial states -/
  I: Set S
  /-- a set of atomic propositions -/
  AP: Type u3
  /-- a labeling function -/
  L: S → AP → Bool --𝒫 (.univ : Set AP)

--attribute [simp low] TransitionSystem.S TransitionSystem.Act

namespace TransitionSystem



def labeling (ts: TransitionSystem) (s: ts.S) : ts.AP → Bool := ts.L s

def LabelingEquiv (ts: TransitionSystem) (s1 s2: ts.S) : Prop := ts.labeling s1 = ts.labeling s2

section Labeling

variable {ts: TransitionSystem} {s1 s2: ts.S}

theorem labelingEquiv_iff_forall_ap : (ts.LabelingEquiv s1 s2) ↔ ∀(ap: ts.AP), ts.labeling s1 ap = ts.labeling s2 ap := by
  dsimp [LabelingEquiv]
  simp [funext_iff]

namespace LabelingEquiv

theorem equivalence : Equivalence ts.LabelingEquiv := by
  constructor
  · intro _; dsimp [LabelingEquiv]
  · intro _ _ lm1;
    dsimp [LabelingEquiv] at lm1 ⊢
    exact lm1.symm
  · dsimp [LabelingEquiv]
    intro _ _ _ lm1 lm2
    exact lm1.trans lm2

end LabelingEquiv

@[reducible]
def toLabelingSetoid (ts: TransitionSystem) : Setoid ts.S where
  r := ts.LabelingEquiv
  iseqv := LabelingEquiv.equivalence


def toLabelingQuotient (ts: TransitionSystem) (s: ts.S) : Quotient ts.toLabelingSetoid := Quotient.mk ts.toLabelingSetoid s



end Labeling



/-- `TS` is called finite if `S`, `Act`, and `AP` are finite. -/
@[mk_iff]
structure IsFinite (TS: TransitionSystem) : Prop where
  finite_s: Finite TS.S
  finite_act: Finite TS.Act
  finite_ap: Finite TS.AP

class ConcreteFinite (TS: TransitionSystem) where
  fintypeS: Fintype TS.S
  fintypeAct: Fintype TS.Act
  fintypeAP: Fintype TS.AP

attribute [reducible, instance] ConcreteFinite.fintypeS
attribute [reducible, instance] ConcreteFinite.fintypeAct
attribute [reducible, instance] ConcreteFinite.fintypeAP

namespace ConcreteFinite

variable {ts: TransitionSystem} [ConcreteFinite ts]



instance (priority := low) decidableEqOfForallAPBool : DecidableEq (ts.AP → Bool) := Fintype.decidablePiFintype

instance (priority := low) decidableLabelingEquiv : DecidableRel (ts.LabelingEquiv) :=
  fun s1 s2 => decidable_of_iff (ts.labeling s1 = ts.labeling s2) (by dsimp [LabelingEquiv]; rfl)

instance (priority := low) decidableEqOfLabelingQuotient : DecidableEq (Quotient ts.toLabelingSetoid) :=
  @Quotient.decidableEq ts.S ts.toLabelingSetoid (inferInstanceAs (DecidableRel (ts.LabelingEquiv)))


end ConcreteFinite



variable (ts: TransitionSystem)

abbrev lts : Cslib.LTS ts.S ts.Act := ⟨ts.tr⟩


section Notation

syntax:52 term:53 " ─⌞" term "⌟→{ " term " } " term:52 : term

macro_rules
  | `( $s1 ─⌞ $act ⌟→{ $ts } $s2 ) => ``( (TransitionSystem.tr $ts) $s1 $act $s2 )

--Cslib.LTS.Tr

end Notation


variable [ConcreteFinite ts]



--set_option trace.Meta.synthInstance true in
instance : IndicatorLike (Quotient ts.toLabelingSetoid) ts.AP where
  coe s := Quotient.liftOn s (ts.labeling) (by
    intro s1 s2 lm1
    change ts.LabelingEquiv s1 s2 at lm1
    dsimp [LabelingEquiv] at lm1
    simpa using lm1 )
  coe_injective s1 s2 := by
    cases s1 using Quotient.inductionOn
    cases s2 using Quotient.inductionOn
    simp
    intro lm1
    simp [funext_iff] at lm1
    apply Quotient.sound
    change ts.LabelingEquiv _ _
    ext x; exact lm1 x


section Notation

syntax:51 " ⟦" term "⟧{" term "} " : term

macro_rules
  | `( ⟦ $s ⟧{ $ts } ) => ``( toLabelingQuotient $ts $s )

end Notation


/-- Not always injective -/
def evalStateToFinset [Fintype ts.AP] (s: ts.S) : Finset (ts.AP) := { ap: ts.AP | ts.labeling s ap = .true }


section Notation

syntax:51 " 𝐿{" term "}⸨ " term " ⸩" : term

macro_rules
  | `( 𝐿{ $ts }⸨ $s ⸩ ) => ``( evalStateToFinset $ts $s )

end Notation


@[scoped grind =]
theorem isSat_iff [DecidableEq ts.AP] (p: Formula ts.AP) (s: ts.S)
  : (⟦s⟧{ts} ⊨ₚ p) ↔ (𝐿{ts}⸨s⸩ ⊨ₚ p) := by
  dsimp [IndicatorLike.coe]
  refine propext_iff.mp ?_
  refine congrFun ?_ p
  refine congrArg _ ?_
  congr
  --dsimp [EvalLike.toIndicator, EvalLike.coe]
  dsimp [toLabelingQuotient]
  --refine DFunLike.ext'_iff.mp ?_
  --refine congrArg Eval.mk ?_
  refine funext ?_
  intro ap
  dsimp [evalStateToFinset, labeling] --, Indicator.fn, Indicator.mk
  simp
  --simp [Indicator.ofFinset_toFinset_leftInverse.eq]



end TransitionSystem


end Nemonuri

end
