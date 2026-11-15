module

public import Nemonuri.Sequence.Basic
public import Mathlib.Data.Seq.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Sequence


structure Potential (α: Type*) where
  getAt? : ℕ → (Option α)
  getAt?_isSeq (n: ℕ) (req: getAt? n = .none) : getAt? (n + 1) = .none

namespace Potential

variable {α: Type*}

def toSeq (p: Potential α) : Stream'.Seq α := ⟨p.getAt?, p.getAt?_isSeq _⟩

def ofSeq (seq: Stream'.Seq α) : Potential α := ⟨seq.val, @seq.property⟩

theorem ofSeq_toSeq_leftInverse : Function.LeftInverse (@ofSeq α) (toSeq) := by
  rintro ⟨g?, _⟩
  dsimp [toSeq, ofSeq]

theorem ofSeq_toSeq_rightInverse : Function.RightInverse (@ofSeq α) (toSeq) := by
  rintro ⟨g?, _⟩
  dsimp [toSeq, ofSeq]

variable (α) in
@[simps]
def equivToSeq : Potential α ≃ Stream'.Seq α where
  toFun := toSeq
  invFun := ofSeq

noncomputable def length? (p: Potential α) : ℕ∞ := p.toSeq.length'

def ofConcrete (seq: Sequence α) : Potential α where
  getAt? := seq.getAt?
  getAt?_isSeq := @seq.add_one_getAt?_none_of_getAt?_none

open Stream'.Seq in
def toConcrete (p: Potential α) (len?: ℕ∞) (req: len? = p.length?) : Sequence α where
  getAt? := p.getAt?
  length? := len?
  length?_getAt? := by
    subst req
    dsimp [length?]
    generalize lm1: p.toSeq = s
    intro i
    have lm2 := p.getAt?_isSeq i
    refine not_iff_not.mp ?_
    simp
    rw [s.length'_le_iff]
    dsimp [TerminatedAt]
    rw [← lm1]
    dsimp [toSeq]
    rfl

noncomputable def toConcrete' (p: Potential α) : Sequence α := p.toConcrete p.length? rfl

theorem ofConcrete_toConcrete'_leftInverse : Function.LeftInverse (@ofConcrete α) toConcrete' := by
  rintro ⟨g?, _⟩
  dsimp [ofConcrete, toConcrete, toConcrete']

theorem ofConcrete_toConcrete'_rightInverse : Function.RightInverse (@ofConcrete α) toConcrete' := by
  intro seq
  refine Sequence.ext ?_
  dsimp [toConcrete', toConcrete, ofConcrete]

variable (α) in
@[simps]
noncomputable def equivToConcrete' : Potential α ≃ Sequence α where
  toFun := toConcrete'
  invFun := ofConcrete
  left_inv := ofConcrete_toConcrete'_leftInverse
  right_inv := ofConcrete_toConcrete'_rightInverse


end Potential


end Nemonuri.Sequence


namespace Stream'.IsSeq

variable {α: Type*}

theorem isSome_of_add_one_isSome {str: Stream' (Option α)} (h: Stream'.IsSeq str) (n: ℕ) (req: (str.get (n + 1)).isSome = .true) : (str.get n).isSome = .true := by
  dsimp [IsSeq] at h
  by_contra lm1
  simp at lm1
  specialize h lm1
  revert req
  simp
  exact h

end Stream'.IsSeq

end
