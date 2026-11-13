module

public import Nemonuri.SequenceProd.Labels
public import Nemonuri.Sequence.Basic
public import Nemonuri.OptionProd.Basic

@[expose] public section

set_option autoImplicit false

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

theorem finite_congr_of_finiteEq (req: sp.toFiniteLabelEq = .labelEq) {fl: FiniteLabel}
  : (sp.toFiniteLabel req = fl) ↔ (sp.fst.toFiniteLabel = fl) ∧ (sp.snd.toFiniteLabel = fl) := by
  rw [fst_self_finiteEq req]
  rw [snd_self_finiteEq req]
  simp

theorem fst_toFiniteLabel_eq_of_toFiniteLabel_eq (req1: sp.toFiniteLabelEq = .labelEq) {fl: FiniteLabel} (req2: sp.toFiniteLabel req1 = fl) : sp.fst.toFiniteLabel = fl :=
  (finite_congr_of_finiteEq req1).mp req2 |>.left

theorem snd_toFiniteLabel_eq_of_toFiniteLabel_eq (req1: sp.toFiniteLabelEq = .labelEq) {fl: FiniteLabel} (req2: sp.toFiniteLabel req1 = fl) : sp.snd.toFiniteLabel = fl :=
  (finite_congr_of_finiteEq req1).mp req2 |>.right


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

theorem empty_congr_of_emptyEq (req: sp.toEmptyLabelEq = .labelEq) {el: EmptyLabel}
  : (sp.toEmptyLabel req = el) ↔ (sp.fst.toEmptyLabel = el) ∧ (sp.snd.toEmptyLabel = el) := by
  rw [fst_self_emptyEq req]
  rw [snd_self_emptyEq req]
  simp

theorem fst_toEmptyLabel_eq_of_toEmptyLabel_eq (req1: sp.toEmptyLabelEq = .labelEq) {el: EmptyLabel} (req2: sp.toEmptyLabel req1 = el) : sp.fst.toEmptyLabel = el :=
  (empty_congr_of_emptyEq req1).mp req2 |>.left

theorem snd_toEmptyLabel_eq_of_toEmptyLabel_eq (req1: sp.toEmptyLabelEq = .labelEq) {el: EmptyLabel} (req2: sp.toEmptyLabel req1 = el) : sp.snd.toEmptyLabel = el :=
  (empty_congr_of_emptyEq req1).mp req2 |>.right



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


def minLength? (sp: SequenceProd α β) : ℕ∞ := Min.min sp.fst.length? sp.snd.length?

theorem minLength?_eq_ite : sp.minLength? = if sp.fst.length? ≤ sp.snd.length? then sp.fst.length? else sp.snd.length? := by
  dsimp [minLength?]
  rw [LinearOrder.min_def]


def minLength (sp: SequenceProd α β) (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite) : ℕ :=
  have lm1 := sp.finite_congr_of_finiteEq req1 |>.mp req2
  Min.min (sp.fst.length lm1.left) (sp.snd.length lm1.right)

@[defeq]
theorem minLength_eq_ite (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite)
  : sp.minLength req1 req2 =
    (have lm1 := sp.finite_congr_of_finiteEq req1 |>.mp req2;
    if (sp.fst.length lm1.left) ≤ (sp.snd.length lm1.right) then (sp.fst.length lm1.left) else (sp.snd.length lm1.right)) :=
  rfl



theorem minLength?_eq_natCast_minLength
  (sp: SequenceProd α β) (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite)
  : sp.minLength? = Nat.cast (sp.minLength req1 req2) := by
  rw [minLength?_eq_ite, minLength_eq_ite]
  extract_lets lm1
  rcases lm1 with ⟨lm1, lm2⟩
  rw [Sequence.length?_eq_natCast_length lm1]
  rw [Sequence.length?_eq_natCast_length lm2]
  symm
  split <;> (
  rename_i lm3; simp; try simp at lm3
  intro lm4
  replace lm4 := Trans.trans lm3 lm4
  simp at lm4 )

theorem minLength?_eq_natCast_of_minLength_eq
  (sp: SequenceProd α β) (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .finite) (fml: ℕ) (req3: sp.minLength req1 req2 = fml)
  : sp.minLength? = ↑fml := by
  rw [← req3]
  exact sp.minLength?_eq_natCast_minLength req1 req2

theorem finite_of_minLength?_eq_natCast_and_finiteEq (sp: SequenceProd α β) (fml: ℕ) (req1: sp.minLength? = ↑fml) (req2: sp.toFiniteLabelEq = .labelEq)
  : sp.toFiniteLabel req2 = .finite := by
  have lm1 := sp.finiteEq_iff_fst_snd_finiteEq.mp req2
  have lm2 := sp.minLength?_eq_ite.symm.trans req1
  split at lm2
  · rw [← (sp.fst_self_finiteEq req2)]
    exact sp.fst.finite_of_length?_eq_natCast lm2
  · rw [← (sp.snd_self_finiteEq req2)]
    exact sp.snd.finite_of_length?_eq_natCast lm2

theorem minLength_eq_of_minLength?_eq_natCast (sp: SequenceProd α β) (fml: ℕ) (req1: sp.minLength? = ↑fml) (req2: sp.toFiniteLabelEq = .labelEq)
  : sp.minLength req2 (sp.finite_of_minLength?_eq_natCast_and_finiteEq fml req1 req2) = fml := by
  rw [← ENat.coe_inj, ← (sp.minLength?_eq_natCast_minLength)]
  exact req1



theorem lt_minLength?_iff_lt_length? {i: ℕ} : ↑i < sp.minLength? ↔ (↑i < sp.fst.length?) ∧ (↑i < sp.snd.length?) := by
  dsimp only [minLength?]
  exact lt_inf_iff

theorem minLength?_pos_iff_length?_pos : (0 < sp.minLength?) ↔ (0 < sp.fst.length?) ∧ (0 < sp.snd.length?) := by
  rw [← ENat.coe_zero]
  exact lt_minLength?_iff_lt_length?


theorem minLength?_pos_of_nonempty (sp: SequenceProd α β) (req1: sp.toEmptyLabelEq = .labelEq) (req2: sp.toEmptyLabel req1 = .nonempty) : 0 < sp.minLength? := by
  rw [minLength?_pos_iff_length?_pos]
  refine ⟨?_, ?_⟩
  · refine sp.fst.length?_pos_of_nonempty ?_
    exact sp.fst_toEmptyLabel_eq_of_toEmptyLabel_eq req1 req2
  · refine sp.snd.length?_pos_of_nonempty ?_
    exact sp.snd_toEmptyLabel_eq_of_toEmptyLabel_eq req1 req2


theorem nonempty_of_minLength?_pos (sp: SequenceProd α β) (req: 0 < sp.minLength?) : ∃(req: sp.toEmptyLabelEq = .labelEq), sp.toEmptyLabel req = .nonempty := by
  rw [minLength?_pos_iff_length?_pos] at req
  rcases req with ⟨lm1, lm2⟩
  replace lm1 := sp.fst.nonempty_of_length?_pos lm1
  replace lm2 := sp.snd.nonempty_of_length?_pos lm2
  refine ⟨?_, ?_⟩
  · rw [sp.emptyEq_iff_fst_snd_emptyEq, lm1, lm2]
  · rw [← sp.fst_self_emptyEq]
    exact lm1

theorem minLength?_pos_iff_nonempty (sp: SequenceProd α β) : (0 < sp.minLength?) ↔ ∃(req: sp.toEmptyLabelEq = .labelEq), sp.toEmptyLabel req = .nonempty := by
  constructor
  · exact sp.nonempty_of_minLength?_pos
  · rintro ⟨lm1, lm2⟩
    exact sp.minLength?_pos_of_nonempty lm1 lm2


def getAt (sp: SequenceProd α β) (i: ℕ) (req: i < sp.minLength?) : Prod α β :=
  have lm1 := lt_minLength?_iff_lt_length?.mp req
  ⟨sp.fst.getAt i lm1.left, sp.snd.getAt i lm1.right⟩


theorem getAt?_eq_ofProd_getAt {i: ℕ} (req: i < sp.minLength?)
  : sp.getAt? i = OptionProd.ofProd (sp.getAt i req) := by
  revert req; simp only [lt_minLength?_iff_lt_length?]; rintro ⟨req1, req2⟩
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

theorem getAt?_fst?_eq_fst_getAt?_at (i: ℕ) : (sp.getAt? i).fst? = (sp.fst.getAt? i) := by
  rw [getAt?_eq_ofProd?_getAt?_at]
  simp only [OptionProd.ofProd?_fst?]

theorem getAt?_snd?_eq_snd_getAt?_at (i: ℕ) : (sp.getAt? i).snd? = (sp.snd.getAt? i) := by
  rw [getAt?_eq_ofProd?_getAt?_at]
  simp only [OptionProd.ofProd?_snd?]


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

theorem getFromLastAt?_fst?_eq_fst_getFromLastAt?_at (i: ℕ) : (sp.getFromLastAt? i).fst? = (sp.fst.getFromLastAt? i) := by
  dsimp [getFromLastAt?]
  simp only [OptionProd.ofProd?_fst?]

theorem getFromLastAt?_snd?_eq_snd_getFromLastAt?_at (i: ℕ) : (sp.getFromLastAt? i).snd? = (sp.snd.getFromLastAt? i) := by
  dsimp [getFromLastAt?]
  simp only [OptionProd.ofProd?_snd?]


def last? (sp: SequenceProd α β) : OptionProd α β := sp.getFromLastAt? 0

theorem last?_fst?_eq_fst_last? : sp.last?.fst? = sp.fst.last? := by
  dsimp [last?, Sequence.last?_eq_getFromLastAt?_zero]
  exact getFromLastAt?_fst?_eq_fst_getFromLastAt?_at 0

theorem last?_snd?_eq_snd_last? : sp.last?.snd? = sp.snd.last? := by
  dsimp [last?, Sequence.last?_eq_getFromLastAt?_zero]
  exact getFromLastAt?_snd?_eq_snd_getFromLastAt?_at 0


theorem getFromLastAt?_eq_none_of_infinite (req1: sp.toFiniteLabelEq = .labelEq) (req2: sp.toFiniteLabel req1 = .infinite) {i: ℕ}
  : sp.getFromLastAt? i = OptionProd.none := by
  obtain ⟨lm1, lm2⟩ := (sp.finite_congr_of_finiteEq req1).mp req2
  dsimp [getFromLastAt?]
  refine OptionProd.ext ?_ ?_
  · simp
    exact Sequence.getFromLastAt?_eq_none_of_infinite lm1
  · simp
    exact Sequence.getFromLastAt?_eq_none_of_infinite lm2

/-
@[mk_iff]
structure IsFinite (sp: SequenceProd α β) : Prop where
  finiteEq: sp.toFiniteLabelEq = .labelEq
  finite: sp.toFiniteLabel finiteEq = .finite
-/

def FiniteSet : Set (SequenceProd α β) := { sp | ∃(finiteEq: sp.toFiniteLabelEq = .labelEq), sp.toFiniteLabel finiteEq = .finite }

/-
@[mk_iff]
structure IsInfinite (sp: SequenceProd α β) : Prop where
  finiteEq: sp.toFiniteLabelEq = .labelEq
  infinite: sp.toFiniteLabel finiteEq = .infinite
-/

def InfiniteSet : Set (SequenceProd α β) := { sp | ∃(finiteEq: sp.toFiniteLabelEq = .labelEq), sp.toFiniteLabel finiteEq = .infinite }


instance : WellFoundedRelation (SequenceProd α β) := invImage (fun (sp: SequenceProd α β) => sp.minLength?) inferInstance


end SequenceProd


end Nemonuri

end
