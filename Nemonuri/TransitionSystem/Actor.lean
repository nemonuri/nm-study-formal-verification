module

public import Nemonuri.Executions.Basic
public import Nemonuri.TransitionSystem.Step

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem


structure ActorStruct (ts: TransitionSystem) where
  stateToActSet (s: ts.S) : Set ts.Act

namespace ActorStruct

variable {ts: TransitionSystem}

def stateToStepRSet (ac: ActorStruct ts) (spr: ts.S) : Set (ts.StepR spr) := { srs: ts.StepR spr | srs.act ∈ ac.stateToActSet spr }

theorem stateToStepRSet_mem_iff (as: ActorStruct ts) (spr: ts.S) (act: ts.Act) (spo: ts.S) (req: spr ─⌞act ⌟→{ ts } spo)
  : (⟨⟨act, spo⟩, req⟩ ∈ (as.stateToStepRSet spr)) ↔ (act ∈ as.stateToActSet spr) := by
  dsimp [stateToStepRSet]
  rfl

end ActorStruct

structure IsActor {ts: TransitionSystem} (as: ts.ActorStruct) : Prop where
  stateToActSet_subset (s: ts.S) : (as.stateToActSet s) ⊆ { act: ts.Act | ∃spo, s ─⌞act ⌟→{ ts } spo }


structure Actor (ts: TransitionSystem) extends toStruct: ts.ActorStruct where
  valid: IsActor toStruct


namespace Actor

structure FiniteStruct (ts: TransitionSystem) extends toBasic: ts.ActorStruct where
  stateToActFinset (s: ts.S) : Finset ts.Act

structure IsFinite {ts: TransitionSystem} (as: FiniteStruct ts) : Prop extends toBasic: IsActor as.toBasic where
  actSet_eq (s: ts.S) : as.stateToActSet s = ↑(as.stateToActFinset s)

structure Finite (ts: TransitionSystem) extends toStruct: FiniteStruct ts where
  valid: IsFinite toStruct

namespace Finite

variable {ts: TransitionSystem}

def stateToAttachedActFinset (af: Actor.Finite ts) (s: ts.S) : Finset ↑(af.stateToActSet s) :=
  have lm1 (a: ts.Act) : (a ∈ af.stateToActFinset s) → (a ∈ af.stateToActSet s) := by
    intro _
    rw [af.valid.actSet_eq s]
    assumption
  (af.stateToActFinset s).attach.map ⟨Subtype.map id lm1, Subtype.map_injective lm1 Function.injective_id⟩

@[reducible]
def stateToActFintype (af: Actor.Finite ts) (s: ts.S) : Fintype ↑(af.stateToActSet s) where
  elems := af.stateToAttachedActFinset s
  complete := by
    simp [stateToAttachedActFinset]
    intro act lm1
    rewrite [af.valid.actSet_eq s] at lm1
    exists act
    exists lm1



end Finite

structure IsDeterministic {ts: TransitionSystem} (as: FiniteStruct ts) : Prop extends toFinite: Actor.IsFinite as where
  actSet_subsingleton (s: ts.S) : (as.stateToActSet s).Subsingleton

structure Deterministic (ts: TransitionSystem) extends toStruct: FiniteStruct ts where
  valid: IsDeterministic toStruct

namespace Deterministic

variable {ts: TransitionSystem}

def toFinite (ad: Deterministic ts) : Actor.Finite ts := ⟨ad.toStruct, ad.valid.toFinite⟩

theorem toFinite_injective : Function.Injective (toFinite: Deterministic ts → Actor.Finite ts) := by
  intro ad1 ad2 lm1
  simp [toFinite] at lm1
  rcases ad1 with ⟨_,_⟩
  rcases ad2 with ⟨_,_⟩
  simpa using lm1

@[reducible]
protected def stateToActFintype (ad: Deterministic ts) (s: ts.S) : Fintype ↑(ad.stateToActSet s) := ad.toFinite.stateToActFintype s

def stateToAct? (ad: Deterministic ts) (s: ts.S) : Option ts.Act :=
  let fs : Finset ts.Act := ad.stateToActFinset s
  if lm1: fs.card = 0 then .none else
  .some (fs.choose (fun _ => True) (by
    classical
    simp at ⊢ lm1
    induction lm2: fs using Finset.induction with
    | empty => contradiction
    | insert act1 fs1 lm3 lm4 =>
      clear lm4
      have lm4 := ad.valid.actSet_subsingleton s
      rw [← lm2]
      subst fs
      rewrite [ad.valid.actSet_eq s] at lm4
      simp [Finset.ext_iff] at lm1
      rcases lm1 with ⟨act2, lm1⟩
      specialize lm4 lm1
      exists act2
      simp [lm1]
      intro act3 lm5
      specialize lm4 lm5
      exact lm4.symm ))



end Deterministic

variable {ts: TransitionSystem}



end Actor


end Nemonuri.TransitionSystem

end
