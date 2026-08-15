module

public import Nemonuri.SequenceProd.Labels
public import Nemonuri.Sequence.Basic

@[expose] public section

namespace Nemonuri

structure SequenceProd (α: Type _) (β: Type _) where
  fst: Sequence α
  snd: Sequence β

namespace SequenceProd

variable {α: Type _} {β: Type _} {sp sp2: SequenceProd α β}

theorem ext (req1: sp.fst.getAt? = sp2.fst.getAt?) (req2: sp.snd.getAt? = sp2.snd.getAt?) : sp = sp2 := by
  rcases sp with ⟨_, _⟩
  rcases sp2 with ⟨_, _⟩
  dsimp at req1 req2
  congr
  · exact Sequence.ext req1
  · exact Sequence.ext req2

theorem ext_iff : (sp = sp2) ↔ ((sp.fst.getAt? = sp2.fst.getAt?) ∧ (sp.snd.getAt? = sp2.snd.getAt?)) := by
  constructor
  · intro lm1
    subst lm1
    constructor <;> rfl
  · rintro ⟨lm1, lm2⟩
    exact ext lm1 lm2

def toFinLabelEq (sp: SequenceProd α β) : LabelEq FiniteLabel := LabelEq.finiteOfENat sp.fst.length? sp.snd.length?

theorem toFinLabel_eq_eq_iff : (sp.toFinLabelEq = .eq) ↔ (sp.fst.toFinLabel = sp.snd.toFinLabel) := by
  dsimp [toFinLabelEq, Sequence.toFinLabel, LabelEq.finiteOfENat, LabelEq.ofENat]
  split <;> rename_i _ lm1 <;> simp at lm1
  · simp
    exact lm1
  · simp
    exact lm1


theorem toFinLabel_eq_ne_iff : (sp.toFinLabelEq = .ne) ↔ (sp.fst.toFinLabel ≠ sp.snd.toFinLabel) := by
  rw [← LabelEq.ne_eq_iff_eq_ne]
  refine Iff.not ?_
  exact toFinLabel_eq_eq_iff

def toFinLabel (_: sp.toFinLabelEq = .eq) : FiniteLabel := sp.fst.toFinLabel

theorem toFinLabel_eq_fst_toFinLabel (req: sp.toFinLabelEq = .eq)
  : toFinLabel req = sp.fst.toFinLabel :=
  rfl

theorem tofinLabel_eq_snd_toFinLabel (req: sp.toFinLabelEq = .eq)
  : toFinLabel req = sp.snd.toFinLabel :=
  calc
    _ = _ := toFinLabel_eq_fst_toFinLabel req
    _ = _ := toFinLabel_eq_eq_iff.mp req


def toEmptyLabelEq (sp: SequenceProd α β) : LabelEq EmptyLabel := LabelEq.emptyOfENat sp.fst.length? sp.snd.length?


theorem toEmptyLabel_eq_eq_iff : (sp.toEmptyLabelEq = .eq) ↔ (sp.fst.toEmptyLabel = sp.snd.toEmptyLabel) := by
  dsimp [toEmptyLabelEq, Sequence.toEmptyLabel, LabelEq.emptyOfENat, LabelEq.ofENat]
  split <;> rename_i _ lm1 <;> simp at lm1
  · simp
    exact lm1
  · simp
    exact lm1

theorem toEmptyLabel_ne_eq_iff : (sp.toEmptyLabelEq = .ne) ↔ (sp.fst.toEmptyLabel ≠ sp.snd.toEmptyLabel) := by
  rw [← LabelEq.ne_eq_iff_eq_ne]
  refine Iff.not ?_
  exact toEmptyLabel_eq_eq_iff

def toEmptyLabel (_: sp.toEmptyLabelEq = .eq) : EmptyLabel := sp.fst.toEmptyLabel

theorem toEmptyLabel_eq_fst_toEmptyLabel (req: sp.toEmptyLabelEq = .eq)
  : toEmptyLabel req = sp.fst.toEmptyLabel :=
  rfl

theorem toEmptyLabel_eq_snd_toEmptyLabel (req: sp.toEmptyLabelEq = .eq)
  : toEmptyLabel req = sp.snd.toEmptyLabel :=
  calc
    _ = _ := toEmptyLabel_eq_fst_toEmptyLabel req
    _ = _ := toEmptyLabel_eq_eq_iff.mp req


end SequenceProd


end Nemonuri

end
