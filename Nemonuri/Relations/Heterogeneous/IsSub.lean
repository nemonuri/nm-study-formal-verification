module

public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Logic.Unique

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

def OfFunction {α β: Sort*} (f: α → β) (a: α) (b: β) : Prop := f a = b

def IsSub {α β: Sort*} (r1 r2: α → β → Prop) : Prop := ∀⦃a: α⦄ ⦃b: β⦄ ⦃_: r1 a b⦄, (r2 a b)

@[defeq]
theorem isSub_def {α β: Sort*} {r1 r2: α → β → Prop} : IsSub r1 r2 = (∀(a: α) (b: β), (r1 a b) → (r2 a b)) := rfl

def IsSubOfFunction {α β: Sort*} (rel: α → β → Prop) (f: α → β) : Prop := IsSub rel (OfFunction f)

namespace IsSubOfFunction

variable {α β: Sort*} {rel: α → β → Prop} {f1 f2: α → β}

theorem fun_apply_eq (h1: IsSubOfFunction rel f1) (h2: IsSubOfFunction rel f2) {a: α} {b: β} (req: rel a b) : f1 a = f2 a := by
  dsimp [IsSubOfFunction, OfFunction, isSub_def] at h1 h2
  specialize h1 a b req
  specialize h2 a b req
  rw [h1, h2]

theorem rel_of_self_apply (h: IsSubOfFunction rel f1) {a: α} {b: β} (req: rel a b) : rel a (f1 a) := by
  dsimp [IsSubOfFunction, OfFunction, isSub_def] at h
  specialize h a b req
  rewrite [h]
  exact req



end IsSubOfFunction

structure IsSubOfEquiv {α β: Sort*} (rel: α → β → Prop) (f: α → β) (fi: β → α) : Prop where
  basic: IsSubOfFunction rel f
  filp: IsSubOfFunction (flip rel) fi


namespace IsSubOfEquiv

variable {α β: Sort*} {rel: α → β → Prop} {f: α → β} {fi: β → α}

theorem fun_apply_inv_apply_eq_self (h: IsSubOfEquiv rel f fi) {a: α} {b: β} (req: rel a b) : fi (f a) = a := by
  rcases h with ⟨lm1, lm2⟩
  dsimp [IsSubOfFunction, OfFunction, isSub_def, Function.flip_def] at lm1 lm2
  specialize lm2 b a req
  specialize lm1 a b req
  conv => rhs; rw [← lm2]
  exact congrArg fi lm1

theorem fun_apply_inv_apply_eq_self' (h: IsSubOfEquiv rel f fi) {a: α} {b: β} (req: rel a b) : f (fi b) = b := by
  rcases h with ⟨lm1, lm2⟩
  dsimp [IsSubOfFunction, OfFunction, isSub_def, Function.flip_def] at lm1 lm2
  specialize lm2 b a req
  specialize lm1 a b req
  conv => rhs; rw [← lm1]
  exact congrArg f lm2

end IsSubOfEquiv


def HasSuperEquiv {α β: Sort*} (rel: α → β → Prop) : Prop := ∃(f: α → β) (fi: β → α), IsSubOfEquiv rel f fi

theorem biUnique_of_hasSuperEquiv {α β: Sort*} {rel: α → β → Prop} (req: HasSuperEquiv rel) : Relator.BiUnique rel := by
  rcases req with ⟨f, fi, lm1, lm2⟩
  dsimp [IsSubOfFunction, isSub_def, OfFunction, Function.flip_def] at lm1 lm2
  refine ⟨?_, ?_⟩
  · intro a1 a2 b lm3 lm4
    have lm2_1 := lm2 b a1 lm3
    have lm2_2 := lm2 b a2 lm4
    exact lm2_1.symm.trans lm2_2
  · intro a b1 b2 lm3 lm4
    have lm1_1 := lm1 a b1 lm3
    have lm1_2 := lm1 a b2 lm4
    exact lm1_1.symm.trans lm1_2

theorem hasSuperEquiv_of_biUnique {α β: Sort*} {rel: α → β → Prop} [Nonempty α] [Nonempty β] (req: Relator.BiUnique rel) : HasSuperEquiv rel := by
  rcases req with ⟨lm1, lm2⟩
  dsimp [HasSuperEquiv]
  dsimp [Relator.LeftUnique] at lm1
  dsimp [Relator.RightUnique] at lm2
  rcases (inferInstance: Nonempty α) with ⟨a⟩
  rcases (inferInstance: Nonempty β) with ⟨b⟩
  classical
  let f1 (a0: α) : β := if lm1: ∃(b0: β), rel a0 b0 then lm1.choose else b
  let f2 (b0: β) : α := if lm1: ∃(a0: α), rel a0 b0 then lm1.choose else a
  exists f1
  exists f2
  refine ⟨?_, ?_⟩ <;> dsimp [IsSubOfFunction, isSub_def, OfFunction, Function.flip_def]
  · intro a2 b2 lm3
    have lm4 := @lm2 a2 b2 (f1 a2) lm3
    symm
    refine lm4 ?_
    subst f1
    dsimp
    have lm5 : ∃(b0: β), rel a2 b0 := Exists.intro b2 lm3
    simp [lm5]
    exact lm5.choose_spec
  · intro b2 a2 lm3
    have lm4 := @lm1 a2 (f2 b2) b2 lm3
    symm
    refine lm4 ?_
    subst f2
    dsimp
    have lm5 : ∃(a0: α), rel a0 b2 := Exists.intro a2 lm3
    simp [lm5]
    exact lm5.choose_spec





    --simp [lm3]
/-
  let f1 := Function.const α b
  let f2 := Function.invFun f1
  exists f1
  exists f2
  refine ⟨?_, ?_⟩ <;> dsimp [IsSubOfFunction, isSub_def, OfFunction, Function.flip_def]
  · intro a2 b2 lm3
    subst f1
    dsimp
    have lm4 := @lm2 (f2 b) b2 b
    subst f2
    dsimp [Function.invFun_eq] at lm4
-/
/-
  exists (fun _ => b)
  exists (fun _ => a)
  refine ⟨?_, ?_⟩ <;> dsimp [IsSubOfFunction, isSub_def, OfFunction, Function.flip_def]
  · intro a2 b2 lm3
-/

/-
theorem hasSuperEquiv_iff_biUnique {α β: Sort*} {rel: α → β → Prop} : HasSuperEquiv rel ↔ Relator.BiUnique rel := by
  constructor
  · rintro ⟨f, fi, lm1, lm2⟩
    dsimp [IsSubOfFunction, isSub_def, OfFunction, Function.flip_def] at lm1 lm2
    refine ⟨?_, ?_⟩
    · intro a1 a2 b lm3 lm4
      have lm2_1 := lm2 b a1 lm3
      have lm2_2 := lm2 b a2 lm4
      exact lm2_1.symm.trans lm2_2
    · intro a b1 b2 lm3 lm4
      have lm1_1 := lm1 a b1 lm3
      have lm1_2 := lm1 a b2 lm4
      exact lm1_1.symm.trans lm1_2
  · rintro ⟨lm1, lm2⟩
    dsimp [HasSuperEquiv]
    dsimp [Relator.LeftUnique] at lm1
    dsimp [Relator.RightUnique] at lm2
    rcases isEmpty_or_nonempty α with ⟨lm3⟩ | ⟨lm3⟩
    · exists (Pi.uniqueOfIsEmpty _).default
      rcases isEmpty_or_nonempty β with ⟨lm4⟩ | ⟨lm4⟩
      · exists (Pi.uniqueOfIsEmpty _).default
        refine ⟨?_, ?_⟩ <;> simp [IsSubOfFunction, IsSub]
      ·
-/
      --rcases isEmpty_or_nonempty β with ⟨lm4⟩ | ⟨lm4⟩
    --<;> rcases isEmpty_or_nonempty β with ⟨lm4⟩ | ⟨lm4⟩
    --·


end Nemonuri.Relations.Heterogeneous

end
