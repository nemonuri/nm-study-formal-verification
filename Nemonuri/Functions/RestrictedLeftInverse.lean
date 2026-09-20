module

public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions

--public import Mathlib.Data.FunLike.Basic

def RestrictedLeftInverse {α β: Sort*} (p: β → Prop) (g: (b: β) → (p b) → α) (f: α → β) (req: (a: α) → p (f a)) : Prop :=
  ∀⦃a: α⦄, g (f a) (req a) = a

namespace RestrictedLeftInverse

def mk (α β: Sort*) (p: β → Prop) (g: (b: β) → (p b) → α) (f: α → β) (req1: (a: α) → p (f a)) (req2: (a: α) → g (f a) (req1 a) = a) := req2

variable {α β: Sort*} {p: β → Prop} {g: (b: β) → (p b) → α} {f: α → β} {req1: (a: α) → p (f a)}

theorem eq (h: RestrictedLeftInverse p g f req1) (a: α) : g (f a) (req1 a) = a := @h a


theorem injective (h: RestrictedLeftInverse p g f req1) : Function.Injective f := by
  intro a1 a2 lm1
  have lm2_1 := h.eq a1
  have lm2_2 := h.eq a2
  suffices goal: g (f a1) (req1 a1) = g (f a2) (req1 a2) from
    calc a1
      _ = _ := lm2_1.symm
      _ = _ := goal
      _ = _ := lm2_2
  have lm3 req3_1 := lm1.rec (motive := fun b0 lm3_1 => (lm3_2: p b0) → (g (f a1) (req1 a1) = g b0 lm3_2)) req3_1
  refine lm3 ?_ _
  · intro _; rfl


end RestrictedLeftInverse


structure RestrictedProd (α: Sort*) (p: α → Prop) (m: (a: α) → Sort*) where
  pos (a: α) (req: p a) : m a
  neg (a: α) (req: ¬p a) : m a

namespace RestrictedProd

variable {α: Sort*} {p: α → Prop} {m: (a: α) → Sort*}

def ofPi (pi: (a: α) → m a) : RestrictedProd α p m where
  pos a _ := pi a
  neg a _ := pi a

def toPi (pr: RestrictedProd α p m) [DecidablePred p] (a: α) : m a :=
  if lm1: p a then pr.pos a lm1 else pr.neg a lm1

@[simps]
def equivOfToPi (α: Sort*) (p: α → Prop) (m: (a: α) → Sort*) [DecidablePred p] : RestrictedProd α p m ≃ ((a: α) → m a) where
  toFun rp := rp.toPi
  invFun pi := .ofPi pi
  left_inv := by
    rintro ⟨rpp, rpn⟩
    dsimp [ofPi, toPi]
    congr
    · simp only [funext_iff]
      intro a lm1
      simp [lm1]
    · simp only [funext_iff]
      intro a lm1
      simp [lm1]
  right_inv := by
    intro pi
    simp only [funext_iff]
    intro a
    dsimp [ofPi, toPi]
    exact ite_self _



end RestrictedProd



end Nemonuri.Functions

end
