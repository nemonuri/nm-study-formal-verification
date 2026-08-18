module

public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace Nemonuri

inductive OptionProd (α: Type _) (β: Type _) where
  | both (fst: α) (snd: β)
  | fst (x: α)
  | snd (x: β)
  | none

namespace OptionProd

variable {α: Type _} {β: Type _} {x1 x2: OptionProd α β} {a: α} {b: β}


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

theorem ofProd_injective : Function.Injective (@ofProd α β) := by
  intro x1 x2 lm1
  cases x1
  cases x2
  simp at lm1
  simpa using lm1

theorem ofProd_inj {x1 x2: Prod α β} : (ofProd x1 = ofProd x2) ↔ (x1 = x2) := ofProd_injective.eq_iff


def ofProd? : Prod (Option α) (Option β) → OptionProd α β
  | ⟨.some a, .some b⟩ => .both a b
  | ⟨.some a, .none⟩ => .fst a
  | ⟨.none, .some b⟩ => .snd b
  | ⟨.none, .none⟩ => .none

def toProd? : OptionProd α β → Prod (Option α) (Option β)
  | .both a b => ⟨.some a, .some b⟩
  | .fst a => ⟨.some a, .none⟩
  | .snd b => ⟨.none, .some b⟩
  | .none => ⟨.none, .none⟩

theorem leftInverse_toProd?_ofProd? : Function.LeftInverse (@toProd? α β) ofProd? := by
  rintro ⟨x1, x2⟩
  cases x1 <;> cases x2 <;> dsimp [toProd?, ofProd?]

theorem rightInverse_toProd?_ofProd? : Function.RightInverse (@toProd? α β) ofProd? := by
  intro x
  cases x <;> dsimp [toProd?, ofProd?]

theorem ofProd?_injective : Function.Injective (@ofProd? α β) := leftInverse_toProd?_ofProd?.injective

theorem toProd?_injective : Function.Injective (@toProd? α β) := rightInverse_toProd?_ofProd?.injective

@[simps]
def equivOfProd? : (Prod (Option α) (Option β)) ≃ OptionProd α β where
  toFun := ofProd?
  invFun := toProd?
  left_inv := leftInverse_toProd?_ofProd?
  right_inv := rightInverse_toProd?_ofProd?


section ToProd?

@[defeq, simp]
theorem both_toProd?_fst : (.both a b : OptionProd α β).toProd?.fst = .some a := rfl

@[defeq, simp]
theorem fst_toProd?_fst : (.fst a : OptionProd α β).toProd?.fst = .some a := rfl

@[defeq, simp]
theorem snd_toProd?_fst : (.snd b : OptionProd α β).toProd?.fst = .none := rfl

@[defeq, simp]
theorem none_toProd?_fst : (.none : OptionProd α β).toProd?.fst = .none := rfl

@[defeq, simp]
theorem both_toProd?_snd : (.both a b : OptionProd α β).toProd?.snd = .some b := rfl

@[defeq, simp]
theorem fst_toProd?_snd : (.fst a : OptionProd α β).toProd?.snd = .none := rfl

@[defeq, simp]
theorem snd_toProd?_snd : (.snd b : OptionProd α β).toProd?.snd = .some b := rfl

@[defeq, simp]
theorem none_toProd?_snd : (.none : OptionProd α β).toProd?.snd = .none := rfl

end ToProd?


section OfProd?

variable {oa: Option α} {ob: Option β}

@[simp]
theorem ofProd?_fst? : (ofProd? (oa, ob)).fst? = oa := by
  cases oa <;> cases ob <;> dsimp [ofProd?]

@[simp]
theorem ofProd?_snd? : (ofProd? (oa, ob)).snd? = ob := by
  cases oa <;> cases ob <;> dsimp [ofProd?]

@[simp]
theorem ofProd?_toProd?_fst : (ofProd? (oa, ob)).toProd?.fst = oa := by
  rw [leftInverse_toProd?_ofProd?]

@[simp]
theorem ofProd?_toProd?_snd : (ofProd? (oa, ob)).toProd?.snd = ob := by
  rw [leftInverse_toProd?_ofProd?]

end OfProd?





end OptionProd


end Nemonuri

end
