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

theorem prod_ext (req1: sp.fst = sp2.fst) (req2: sp.snd = sp2.snd) : sp = sp2 := by
  refine ext ?_ ?_ <;> rw [← Sequence.ext_iff]
  · exact req1
  · exact req2

theorem prod_ext_iff : (sp = sp2) ↔ ((sp.fst = sp2.fst) ∧ (sp.snd = sp2.snd)) := by
  constructor
  · intro lm1
    subst lm1
    constructor <;> rfl
  · rintro ⟨lm1, lm2⟩
    exact prod_ext lm1 lm2


def toFiniteLabelEq (sp: SequenceProd α β) : LabelEq FiniteLabel := LabelEq.finiteOfENat sp.fst.length? sp.snd.length?

theorem finiteEq_iff_fst_snd_finiteEq : (sp.toFiniteLabelEq = .labelEq) ↔ (sp.fst.toFiniteLabel = sp.snd.toFiniteLabel) := by
  dsimp [toFiniteLabelEq, Sequence.toFiniteLabel, LabelEq.finiteOfENat, LabelEq.ofENat]
  split <;> rename_i _ lm1 <;> simp at lm1
  · simp
    exact lm1
  · simp
    exact lm1


theorem finiteEq_iff_fst_snd_finiteNe : (sp.toFiniteLabelEq = .labelNe) ↔ (sp.fst.toFiniteLabel ≠ sp.snd.toFiniteLabel) := by
  rw [← LabelEq.ne_labelEq_iff_eq_labelNe]
  refine Iff.not ?_
  exact finiteEq_iff_fst_snd_finiteEq

def toFiniteLabel (sp: SequenceProd α β) (_: sp.toFiniteLabelEq = .labelEq) : FiniteLabel := sp.fst.toFiniteLabel

theorem fst_self_finiteEq (req: sp.toFiniteLabelEq = .labelEq)
  : sp.fst.toFiniteLabel = sp.toFiniteLabel req :=
  rfl

theorem snd_self_finiteEq (req: sp.toFiniteLabelEq = .labelEq)
  : sp.snd.toFiniteLabel = sp.toFiniteLabel req :=
  calc
    _ = _ := finiteEq_iff_fst_snd_finiteEq.mp req |>.symm
    _ = _ := fst_self_finiteEq req


def toEmptyLabelEq (sp: SequenceProd α β) : LabelEq EmptyLabel := LabelEq.emptyOfENat sp.fst.length? sp.snd.length?


theorem emptyEq_iff_fst_snd_emptyEq : (sp.toEmptyLabelEq = .labelEq) ↔ (sp.fst.toEmptyLabel = sp.snd.toEmptyLabel) := by
  dsimp [toEmptyLabelEq, Sequence.toEmptyLabel, LabelEq.emptyOfENat, LabelEq.ofENat]
  split <;> rename_i _ lm1 <;> simp at lm1
  · simp
    exact lm1
  · simp
    exact lm1

theorem emptyNe_iff_fst_snd_emptyNe : (sp.toEmptyLabelEq = .labelNe) ↔ (sp.fst.toEmptyLabel ≠ sp.snd.toEmptyLabel) := by
  rw [← LabelEq.ne_labelEq_iff_eq_labelNe]
  refine Iff.not ?_
  exact emptyEq_iff_fst_snd_emptyEq

def toEmptyLabel (sp: SequenceProd α β) (_: sp.toEmptyLabelEq = .labelEq) : EmptyLabel := sp.fst.toEmptyLabel

theorem fst_self_emptyEq (req: sp.toEmptyLabelEq = .labelEq)
  : sp.fst.toEmptyLabel = sp.toEmptyLabel req :=
  rfl

theorem snd_self_emptyEq (req: sp.toEmptyLabelEq = .labelEq)
  : sp.snd.toEmptyLabel = sp.toEmptyLabel req :=
  calc
    _ = _ := emptyEq_iff_fst_snd_emptyEq.mp req |>.symm
    _ = _ := sp.fst_self_emptyEq req


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



def head (sp: SequenceProd α β) (req1: sp.toEmptyLabelEq = .labelEq) (req2: sp.toEmptyLabel req1 = .nonempty) : Prod α β :=
  have lm1 := sp.fst_self_emptyEq req1 |>.trans req2
  have lm2 := sp.snd_self_emptyEq req1 |>.trans req2
  ⟨sp.fst.head lm1, sp.snd.head lm2⟩

theorem head?_eq_ofProd_head (req1: sp.toEmptyLabelEq = .labelEq) (req2: sp.toEmptyLabel req1 = .nonempty)
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

@[defeq]
theorem getAt?_eq_ofProd?_getAt?_at (i: ℕ) : sp.getAt? i = .ofProd? (sp.fst.getAt? i, sp.snd.getAt? i) := rfl

@[defeq]
theorem getAt?_eq_ofProd?_getAt? : sp.getAt? = (fun (i: ℕ) => .ofProd? (sp.fst.getAt? i, sp.snd.getAt? i)) := rfl


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



theorem getAt?_ext (req: sp.getAt? = sp2.getAt?) : sp = sp2 := by
  dsimp only [getAt?_eq_ofProd?_getAt?] at req
  rewrite [funext_iff] at req
  conv at req =>
    conv =>
      arg 2
      rw [OptionProd.ext_iff]
      simp
    rw [forall_and]
    simp only [← funext_iff]
  rcases req with ⟨lm1, lm2⟩
  exact SequenceProd.ext lm1 lm2

theorem getAt?_ext_iff : (sp = sp2) ↔ (sp.getAt? = sp2.getAt?) := ⟨fun lm1 => congrArg _ lm1, getAt?_ext⟩



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
