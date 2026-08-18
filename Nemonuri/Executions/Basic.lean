module

public import Nemonuri.SequenceProd.Basic
public import Nemonuri.TransitionSystem

@[expose] public section

/-!

### Definition 2.6. Execution Fragment

-/

namespace Nemonuri.TransitionSystem

/-
structure IsExecutionFragment {ts: TransitionSystem} (sp: SequenceProd ts.S ts.Act) : Prop where
  length_eq : sp.fst.length? = sp.snd.length? + 1
--  firstState_eq : raw.states[0] = raw.firstState
--  lastState_eq : raw.states[raw.states.length - 1] = raw.lastState
  states_actions_valid (i: ℕ) (h: i < sp.snd.length?) : sp.fst.getAt i  ─⌞(raw.actions[i])⌟→{ts} raw.states[i+1]
-/


end Nemonuri.TransitionSystem

end
