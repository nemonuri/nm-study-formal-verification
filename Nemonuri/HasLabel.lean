module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.FunLike.Basic


@[expose] public section

namespace Nemonuri

class HasLabel (Label: Type _) [DecidableEq Label] [Fintype Label] (T: Type _)  where
  toLabel (t: T) : Label

namespace HasLabel

section Definition

variable (Label: Type _) [DecidableEq Label] [Fintype Label] {T1: Type _} [HasLabel Label T1] {T2: Type _} [HasLabel Label T2]

def Preserves (f: (_: T1) → T2) : Prop := ∀ ⦃x: T1⦄, (toLabel x : Label) = (toLabel (f x))

structure LabelHom (T1: Type _) [HasLabel Label T1] (T2: Type _) [HasLabel Label T2] where
  toFun: T1 → T2
  preserves: Preserves Label toFun

class IsLabelHomLike
  (F: Type _) (Label T1 T2: outParam (Type _))
  [DecidableEq Label] [Fintype Label] [HasLabel Label T1] [HasLabel Label T2] [FunLike F T1 T2] : Prop where
  preserves (f: F) : Preserves Label (f: T1 → T2)

end Definition

variable {Label: Type _} [DecidableEq Label] [Fintype Label]
         {T1: Type _} [HasLabel Label T1] {T2: Type _} [HasLabel Label T2] {T3: Type _} [HasLabel Label T3]

theorem preserves_def {f: T1 → T2} : Preserves Label f ↔ ∀(x: T1), (toLabel x : Label) = (toLabel (f x)) := Iff.rfl

namespace Preserves

theorem mk (f: T1 → T2) (req: ∀(x: T1), (toLabel x : Label) = (toLabel (f x))) : Preserves Label f := req

theorem cancel (f: T1 → T2) (h: Preserves Label f) (x: T1) : (toLabel (f x)) = (toLabel x : Label) := @h x |>.symm

theorem comp {fl: T2 → T3} {fr: T1 → T2} (h1: Preserves Label fl) (h2: Preserves Label fr) : Preserves Label (fl ∘ fr) := by
  revert h1 h2; dsimp [Preserves]
  intro h1 h2 x
  specialize @h2 x
  specialize @h1 (fr x)
  exact Eq.trans h2 h1

end Preserves



namespace LabelHom


instance toFunlike : FunLike (LabelHom Label T1 T2) T1 T2 where
  coe lh := lh.toFun
  coe_injective lh1 lh2 := by cases lh1; cases lh2; dsimp; intro lm1; subst lm1; rfl

instance is_labelHomLike : IsLabelHomLike (LabelHom Label T1 T2) Label T1 T2 where
  preserves lh := lh.preserves



@[defeq, simp]
theorem coe_mk (f: T1 → T2) (req: Preserves Label f) : ((LabelHom.mk f req): T1 → T2) = f := rfl

@[defeq, simp]
theorem toFun_eq_coe (f: LabelHom Label T1 T2) : f.toFun = f := rfl

@[ext]
theorem ext ⦃f1 f2: LabelHom Label T1 T2⦄ (h: ∀x, f1 x = f2 x) : f1 = f2 := DFunLike.ext _ _ h

@[defeq, simp]
theorem mk_coe (f: LabelHom Label T1 T2) (req: Preserves Label f) : (LabelHom.mk f req) = f :=
  LabelHom.ext (fun _ => rfl)

protected def copy (f1: LabelHom Label T1 T2) (f2: T1 → T2) (h: f2 = f1) : LabelHom Label T1 T2 where
  toFun := f2
  preserves := h.symm ▸ f1.preserves

section

omit [HasLabel Label T1] [HasLabel Label T2]

@[simp]
theorem coe_copy {_: HasLabel Label T1} {_: HasLabel Label T2} (f1: LabelHom Label T1 T2) (f2: T1 → T2) (h: f2 = f1)
  : (f1.copy f2 h) = f2 :=
  rfl

theorem coe_copy_eq {_: HasLabel Label T1} {_: HasLabel Label T2} (f1: LabelHom Label T1 T2) (f2: T1 → T2) (h: f2 = f1)
  : f1.copy f2 h = f1 :=
  DFunLike.ext' h

end

@[simps, implicit_reducible]
def id (Label: Type _) [DecidableEq Label] [Fintype Label] (T: Type _) [HasLabel Label T] : LabelHom Label T T where
  toFun x := x
  preserves _ := rfl

@[simp]
theorem coe_id : (LabelHom.id Label T1 : T1 → T1) = _root_.id := rfl


@[implicit_reducible]
def comp (lhl: LabelHom Label T2 T3) (lhr: LabelHom Label T1 T2) : LabelHom Label T1 T3 where
  toFun x := lhl (lhr x)
  preserves := by
    refine Preserves.comp ?_ ?_
    · exact lhl.preserves
    · exact lhr.preserves

@[defeq]
theorem coe_comp (lhl: LabelHom Label T2 T3) (lhr: LabelHom Label T1 T2)
  : ↑(lhl.comp lhr) = lhl ∘ lhr :=
  rfl

@[defeq]
theorem comp_apply (lhl: LabelHom Label T2 T3) (lhr: LabelHom Label T1 T2) (x: T1) : lhl.comp lhr x = lhl (lhr x) := rfl

@[defeq]
theorem comp_assoc {T4: Type _} [HasLabel Label T4] (lh1: LabelHom Label T1 T2) (lh2: LabelHom Label T2 T3) (lh3: LabelHom Label T3 T4)
  : (lh3.comp lh2).comp lh1 = lh3.comp (lh2.comp lh1) := rfl

@[defeq, simp]
theorem comp_id (f: LabelHom Label T1 T2) : f.comp (LabelHom.id Label T1) = f := LabelHom.ext (fun _ => rfl)

@[defeq, simp]
theorem id_comp (f: LabelHom Label T1 T2) : (LabelHom.id Label T2).comp f = f := LabelHom.ext (fun _ => rfl)

end LabelHom


namespace IsLabelHomLike

variable {F: Type _} {T1 T2 Label: outParam (Type _)} [DecidableEq Label] [Fintype Label] [HasLabel Label T1] [HasLabel Label T2] [FunLike F T1 T2]

@[coe]
def toLabelHom [IsLabelHomLike F Label T1 T2] (f: F) : LabelHom Label T1 T2 where
  toFun := f
  preserves := IsLabelHomLike.preserves f

instance [IsLabelHomLike F Label T1 T2] : CoeHead F (LabelHom Label T1 T2) := ⟨toLabelHom⟩

@[defeq, simp]
theorem coe_coe [IsLabelHomLike F Label T1 T2] (f: F) : ((f: LabelHom Label T1 T2): T1 → T2) = f := rfl


end IsLabelHomLike


end HasLabel

end Nemonuri

end
