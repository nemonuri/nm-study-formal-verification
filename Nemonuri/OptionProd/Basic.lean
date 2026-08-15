module

@[expose] public section

namespace Nemonuri

inductive OptionProd (α: Type _) (β: Type _) where
  | both (fst: α) (snd: β)
  | fst (x: α)
  | snd (x: β)
  | none

namespace OptionProd

variable {α: Type _} {β: Type _} {x1 x2: OptionProd α β} {a: α} {b: β}

@[simp]
def fst? : OptionProd α β → Option α
  | both x _ => .some x
  | fst x => .some x
  | _ => .none

@[defeq, simp]
theorem both_fst? : (OptionProd.both a b).fst? = .some a := by dsimp [fst?]

@[defeq, simp]
theorem fst_fst? : (@OptionProd.fst α β a).fst? = .some a := by dsimp [fst?]

@[defeq, simp]
theorem snd_fst? : (@OptionProd.snd α β b).fst? = .none := by dsimp [fst?]

@[defeq, simp]
theorem none_fst? : (@OptionProd.none α β).fst? = .none := by dsimp [fst?]


def snd? : OptionProd α β → Option β
  | both _ x => .some x
  | snd x => .some x
  | _ => .none

@[defeq, simp]
theorem both_snd? : (OptionProd.both a b).snd? = .some b := by dsimp [snd?]

@[defeq, simp]
theorem fst_snd? : (@OptionProd.fst α β a).snd? = .none := by dsimp [snd?]

@[defeq, simp]
theorem snd_snd? : (@OptionProd.snd α β b).snd? = .some b := by dsimp [snd?]

@[defeq, simp]
theorem none_snd? : (@OptionProd.none α β).snd? = .none := by dsimp [snd?]


theorem ext (req1: x1.fst? = x2.fst?) (req2: x1.snd? = x2.snd?) : x1 = x2 := by
  cases x1 <;> cases x2 <;> simp at req1 <;> simp at req2
  · subst req1
    subst req2
    rfl
  · subst req1
    rfl
  · subst req2
    rfl
  · rfl


theorem ext_iff : (x1 = x2) ↔ ((x1.fst? = x2.fst?) ∧ (x1.snd? = x2.snd?)) := by
  constructor
  · intro lm1; subst lm1; simp
  · rintro ⟨lm1, lm2⟩
    exact ext lm1 lm2


def ofProd : Prod α β → OptionProd α β
  | ⟨a, b⟩ => .both a b

@[defeq, simp]
theorem ofProd_eq_both : ofProd (a, b) = .both a b := rfl

theorem ofProd_inj : Function.Injective (@ofProd α β) := by
  intro x1 x2 lm1
  cases x1
  cases x2
  simp at lm1
  simpa using lm1


end OptionProd


end Nemonuri

end
