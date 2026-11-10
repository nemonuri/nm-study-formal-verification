module


public meta import Nemonuri.TransitionSystem.Attributes
public import Nemonuri.TransitionSystem.Basic


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], 2.1 Transition Systems, p.19

-/


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem


variable {ts: TransitionSystem}


/-!

### Definition 2.3. Direct Predecessors and Successors

-/

variable (ts) in
def directSuccessorSetOfAct (s: ts.S) (α: ts.Act) : Set ts.S := { s': ts.S | s ─⌞α⌟→{ts} s' }

variable (ts) in
def directPredecessorSetOfAct (s: ts.S) (α: ts.Act) : Set ts.S := { s': ts.S | s' ─⌞α⌟→{ts} s }

section Notation

syntax:61 " 𝑃𝑜𝑠𝑡{" term "}⸨" term "," term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒{" term "}⸨" term "," term "⸩ " : term

macro_rules
  | `( 𝑃𝑜𝑠𝑡{ $ts }⸨ $s , $α ⸩ ) => ``( directSuccessorSetOfAct $ts $s $α )
  | `( 𝑃𝑟𝑒{ $ts }⸨ $s , $α ⸩ ) => ``( directPredecessorSetOfAct $ts $s $α )

end Notation

@[det_norm]
theorem directSuccessorSetOfAct_mem {s: ts.S} {α: ts.Act} {spo: ts.S} : spo ∈ 𝑃𝑜𝑠𝑡{ts}⸨s, α⸩ ↔ (s ─⌞α⌟→{ts} spo) := by
  dsimp [directSuccessorSetOfAct]
  rfl

@[det_norm]
theorem directPredecessorSetOfAct_mem {s: ts.S} {α: ts.Act} {spr: ts.S} : spr ∈ 𝑃𝑟𝑒{ts}⸨s, α⸩ ↔ (spr ─⌞α⌟→{ts} s) := by
  dsimp [directPredecessorSetOfAct]
  rfl



variable (ts) in
def directSuccessorSet (s: ts.S) : Set ts.S := ⋃ α: ts.Act, 𝑃𝑜𝑠𝑡{ts}⸨s, α⸩

variable (ts) in
def directPredecessorSet (s: ts.S) : Set ts.S := ⋃ α: ts.Act, 𝑃𝑟𝑒{ts}⸨s, α⸩


section Notation

syntax:61 " 𝑃𝑜𝑠𝑡{" term "}⸨" term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒{" term "}⸨" term "⸩ " : term

macro_rules
  | `( 𝑃𝑜𝑠𝑡{ $ts }⸨ $s ⸩ ) => ``( directSuccessorSet $ts $s )
  | `( 𝑃𝑟𝑒{ $ts }⸨ $s ⸩ ) => ``( directPredecessorSet $ts $s )

end Notation


@[det_norm]
theorem directSuccessorSet_mem {s: ts.S} {spo: ts.S} : spo ∈ 𝑃𝑜𝑠𝑡{ts}⸨s⸩ ↔ ∃act, (s ─⌞act⌟→{ts} spo) := by
  simp [directSuccessorSet, det_norm]

@[det_norm]
theorem directPredecessorSet_mem {s: ts.S} {spr: ts.S} : spr ∈ 𝑃𝑟𝑒{ts}⸨s⸩ ↔ ∃act, (spr ─⌞act⌟→{ts} s) := by
  simp [directPredecessorSet, det_norm]


variable (ts) in
def directSuccessorSetOfActOfSet (C: Set ts.S) (α: ts.Act) : Set ts.S := ⋃ s ∈ C, 𝑃𝑜𝑠𝑡{ts}⸨s, α⸩

variable (ts) in
def directPredecessorSetOfActOfSet (C: Set ts.S) (α: ts.Act) : Set ts.S := ⋃ s ∈ C, 𝑃𝑟𝑒{ts}⸨s, α⸩

variable (ts) in
def directSuccessorOfSet (C: Set ts.S) : Set ts.S := ⋃ s ∈ C, 𝑃𝑜𝑠𝑡{ts}⸨s⸩

variable (ts) in
def directPredecessorOfSet (C: Set ts.S) : Set ts.S := ⋃ s ∈ C, 𝑃𝑟𝑒{ts}⸨s⸩


section Notation

syntax:61 " 𝑃𝑜𝑠𝑡ᵤ{" term "}⸨" term "," term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒ᵤ{" term "}⸨" term "," term "⸩ " : term
syntax:61 " 𝑃𝑜𝑠𝑡ᵤ{" term "}⸨" term "⸩ " : term
syntax:61 " 𝑃𝑟𝑒ᵤ{" term "}⸨" term "⸩ " : term

macro_rules
  | `( 𝑃𝑜𝑠𝑡ᵤ{ $ts }⸨ $C, $α ⸩ ) => ``( directSuccessorSetOfActOfSet $ts $C $α )
  | `( 𝑃𝑟𝑒ᵤ{ $ts }⸨ $C, $α ⸩ ) => ``( directPredecessorSetOfActOfSet $ts $C $α )
  | `( 𝑃𝑜𝑠𝑡ᵤ{ $ts }⸨ $C ⸩ ) => ``( directSuccessorOfSet $ts $C )
  | `( 𝑃𝑟𝑒ᵤ{ $ts }⸨ $C ⸩ ) => ``( directPredecessorOfSet $ts $C )

end Notation

@[det_norm]
theorem directSuccessorSetOfActOfSet_mem {C: Set ts.S} {α: ts.Act} {spo: ts.S} : spo ∈ 𝑃𝑜𝑠𝑡ᵤ{ts}⸨C, α⸩ ↔ ∃spr ∈ C, (spr ─⌞α⌟→{ts} spo) := by
  simp [directSuccessorSetOfActOfSet, det_norm]

@[det_norm]
theorem directPredecessorSetOfActOfSet_mem {C: Set ts.S} {α: ts.Act} (spr: ts.S) : spr ∈ 𝑃𝑟𝑒ᵤ{ts}⸨C, α⸩ ↔ ∃spo ∈ C, (spr ─⌞α⌟→{ts} spo) := by
  simp [directPredecessorSetOfActOfSet, det_norm]

@[det_norm]
theorem directSuccessorOfSet_mem {C: Set ts.S} {spo: ts.S} : spo ∈ 𝑃𝑜𝑠𝑡ᵤ{ts}⸨C⸩ ↔ ∃spr ∈ C, ∃act, (spr ─⌞act⌟→{ts} spo) := by
  simp [directSuccessorOfSet, det_norm]

@[det_norm]
theorem directPredecessorOfSet_mem {C: Set ts.S} (spr: ts.S) : spr ∈ 𝑃𝑟𝑒ᵤ{ts}⸨C⸩ ↔ ∃spo ∈ C, ∃act, (spr ─⌞act⌟→{ts} spo) := by
  simp [directPredecessorOfSet, det_norm]


/-!

### Definition 2.4. Terminal State

-/

variable (ts) in
def IsTerminal (s: ts.S) : Prop := 𝑃𝑜𝑠𝑡{ts}⸨s⸩ = ∅

theorem isTerminal_iff {s: ts.S} : ts.IsTerminal s ↔ ∀act spo, ¬(s ─⌞act⌟→{ts} spo) := by
  dsimp [IsTerminal]
  conv =>
    lhs
    rw [Set.ext_iff]
    simp [det_norm]
    rw [forall_comm]


/-!

### Definition 2.5. Deterministic Transition System

-/

variable (ts) in
def IsDirectSuccessorSetOfActSubsingleton (s: ts.S) (α: ts.Act) : Prop := (𝑃𝑜𝑠𝑡{ts}⸨s, α⸩).Subsingleton

variable (ts) in
def IsDirectSuccessorLabelingSubsingleton [Fintype ts.AP] (s: ts.S) (A: ts.AP → Bool) : Prop := ((𝑃𝑜𝑠𝑡{ts}⸨s⸩) ∩ { s': ts.S | (𝐿{ts}⸨s'⸩) = { ap | A ap = .true } }).Subsingleton

structure IsActionDeterministic (ts: TransitionSystem) : Prop where
  initial_subsingleton : ts.I.Subsingleton
  post_subsingleton (s: ts.S) (α: ts.Act) : ts.IsDirectSuccessorSetOfActSubsingleton s α

structure IsAPDeterministic (ts: TransitionSystem) [Fintype ts.AP] : Prop where
  initial_subsingleton : ts.I.Subsingleton
  post_subsingleton (s: ts.S) (A: ts.AP → Bool) : ts.IsDirectSuccessorLabelingSubsingleton s A



@[det_norm]
theorem isDirectSuccessorSetOfActSubsingleton_iff {s} {act}
  : (ts.IsDirectSuccessorSetOfActSubsingleton s act) ↔ (Set.Subsingleton { spo | (s ─⌞act⌟→{ts} spo) }) := by
  dsimp [IsDirectSuccessorSetOfActSubsingleton, Set.Subsingleton]
  simp [det_norm]

@[det_norm]
theorem isDirectSuccessorLabelingSubsingleton_iff [Fintype ts.AP] {s: ts.S} {A: ts.AP → Bool}
  : ts.IsDirectSuccessorLabelingSubsingleton s A ↔ (Set.Subsingleton { spo: ts.S | ∃(act: ts.Act), (s ─⌞act⌟→{ts} spo) ∧ (ts.L spo = A)}) := by
  dsimp [IsDirectSuccessorLabelingSubsingleton, evalStateToFinset, labeling, Set.Subsingleton]
  simp [det_norm, Set.ext_iff, funext_iff]






end Nemonuri.TransitionSystem

end
