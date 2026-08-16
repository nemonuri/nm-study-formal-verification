module

public import Nemonuri.SequenceProd.Labels
public import Nemonuri.Sequence.Basic
public import Nemonuri.OptionProd.Basic

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


def head? (sp: SequenceProd α β) : OptionProd α β :=
  match sp.fst.head?, sp.snd.head? with
  | .some fst, .some snd => .both fst snd
  | .some x, .none => .fst x
  | .none, .some x => .snd x
  | .none, .none => .none

theorem head?_eq_ofProd? : sp.head? = OptionProd.ofProd? (sp.fst.head?, sp.snd.head?) := by
  rw [← OptionProd.equivOfProd?.symm.injective.eq_iff]
  simp
  rw [OptionProd.leftInverse_toProd?_ofProd? _]
  dsimp [head?]
  split <;> rename_i lm1 lm2 <;> simp [OptionProd.toProd?, lm1, lm2]



def head (sp: SequenceProd α β) (req1: sp.toEmptyLabelEq = .eq) (req2: sp.toEmptyLabel req1 = .nonempty) : Prod α β :=
  have lm1 := sp.toEmptyLabel_eq_fst_toEmptyLabel req1 |>.symm.trans req2
  have lm2 := sp.toEmptyLabel_eq_snd_toEmptyLabel req1 |>.symm.trans req2
  ⟨sp.fst.head lm1, sp.snd.head lm2⟩

theorem head?_eq_ofProd_head (req1: sp.toEmptyLabelEq = .eq) (req2: sp.toEmptyLabel req1 = .nonempty)
  : sp.head? = OptionProd.ofProd (sp.head req1 req2) := by
  rcases lm1: sp.head req1 req2 with ⟨fst, snd⟩
  dsimp
  dsimp [head] at lm1
  simp [Prod.ext_iff] at lm1
  rcases lm1 with ⟨lm1, lm2⟩
  rewrite [← Option.some_inj, ← Sequence.head?_eq_some_head] at lm1 lm2
  dsimp [head?]
  simp only [lm1, lm2]


def getAt? (sp: SequenceProd α β) (i: ℕ) : OptionProd α β := OptionProd.ofProd? ⟨sp.fst.getAt? i, sp.snd.getAt? i⟩

def getAt (sp: SequenceProd α β) (i: ℕ) (req1: i < sp.fst.length?) (req2: i < sp.snd.length?) : Prod α β := ⟨sp.fst.getAt i req1, sp.snd.getAt i req2⟩

theorem getAt?_eq_ofProd_getAt {i: ℕ} (req1: i < sp.fst.length?) (req2: i < sp.snd.length?)
  : sp.getAt? i = OptionProd.ofProd (sp.getAt i req1 req2) := by
  dsimp [getAt]
  dsimp [getAt?]
  rw [← OptionProd.equivOfProd?.symm.injective.eq_iff]
  simp only [OptionProd.equivOfProd?_symm_apply]
  rw [OptionProd.leftInverse_toProd?_ofProd? _]
  dsimp [OptionProd.toProd?]
  rw [Prod.ext_iff]
  dsimp
  refine And.intro ?_ ?_
  · exact Sequence.getAt?_eq_some_getAt req1
  · exact Sequence.getAt?_eq_some_getAt req2


def getAt?Flip (i: ℕ) {α β: Type _} (sp: SequenceProd α β) : OptionProd α β := sp.getAt? i

@[defeq]
theorem getAt?Flip_eq_getAt? {i: ℕ} : getAt?Flip i sp = sp.getAt? i := rfl

theorem head?_eq_getAt?Flip_zero : @head? = @getAt?Flip 0 := by
  ext α β sp
  dsimp [getAt?Flip_eq_getAt?]
  dsimp [getAt?]
  simp only [← Sequence.head?_eq_getAt?_zero]
  refine OptionProd.ext ?_ ?_
  · simp only [OptionProd.ofProd?_fst?]
    dsimp [head?]
    split <;> rename_i lm1 _ <;> simp [lm1]
  · simp only [OptionProd.ofProd?_snd?]
    dsimp [head?]
    split <;> rename_i _ lm2 <;> simp [lm2]

def getFromEndAt? (sp: SequenceProd α β) (i: ℕ) (sentinel?: OptionProd α β) : OptionProd α β :=
  let x := sentinel?.toProd?
  OptionProd.ofProd? ⟨sp.fst.getFromEndAt? i x.fst, sp.snd.getFromEndAt? i x.snd⟩

def getFromLastAt? (sp: SequenceProd α β) (i: ℕ) : OptionProd α β :=
  OptionProd.ofProd? ⟨sp.fst.getFromLastAt? i, sp.snd.getFromLastAt? i⟩

end SequenceProd


end Nemonuri

end
