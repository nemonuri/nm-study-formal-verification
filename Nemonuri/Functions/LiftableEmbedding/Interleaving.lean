module

public import Nemonuri.Functions.LiftableEmbedding.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding


inductive Interleaving.{uu, us} (Univ: Sort uu) : List (Sort us) → Sort _ where
  | nil: Interleaving Univ []
  | cons {sub: Sort us} (lem: LiftableEmbedding sub Univ) {subs: List (Sort us)} : Interleaving Univ subs → Interleaving Univ (sub::subs)

namespace Interleaving

universe uu us
variable {Univ: Sort uu} {ss: List (Sort us)}

def subs (_: Interleaving Univ ss) : List (Sort us) := ss

def length (il: Interleaving Univ ss) : Nat := il.subs.length

@[defeq]
theorem length_def {il: Interleaving Univ ss} : il.length = ss.length := rfl

@[defeq]
theorem nil_length_eq_zero : (.nil : Interleaving Univ []).length = 0 := by
  dsimp [length_def]

instance nil_subsingleton : Subsingleton (Interleaving Univ []) where
  allEq := by rintro ⟨⟩ ⟨⟩; rfl

@[defeq]
theorem cons_length_eq {s: Sort us} {lem: LiftableEmbedding s Univ} {ss: List (Sort us)} {il: Interleaving Univ ss}
  : (cons lem il).length = il.length + 1 := by
  dsimp [length_def]


def GetSub (il: Interleaving Univ ss) (n: Fin il.length) : Sort us := il.subs.get n

@[defeq]
theorem cons_getSub_eq {s: Sort us} {lem: LiftableEmbedding s Univ} {ss: List (Sort us)} {il: Interleaving Univ ss} {n: Fin il.length}
  : (cons lem il).GetSub (Fin.mk (n+1) (by simp [cons_length_eq])) = il.GetSub n := by
  dsimp [GetSub, subs]


def getLiftableEmbeddingAt (ss: List (Sort us)) (il: Interleaving Univ ss) (n: Fin il.length) : LiftableEmbedding (il.GetSub n) Univ :=
  match ss, il with
  | [], .nil => Fin.elim0 (nil_length_eq_zero ▸ n)
  | s::ss, .cons lem il =>
  match n with
  | ⟨0, _⟩ => lem
  | ⟨n+1, lm1⟩ =>
    have lm2: n < il.length := by simpa [cons_length_eq] using lm1
    getLiftableEmbeddingAt ss il ⟨n, lm2⟩


def getLiftableEmbedding (il: Interleaving Univ ss) (n: Fin il.length) : LiftableEmbedding (il.GetSub n) Univ := il.getLiftableEmbeddingAt ss n


inductive MapsToIsLiftable {Univ: Sort uu} (uv: Univ) : {ss: List (Sort us)} → Interleaving Univ ss → List Bool → Prop where
  | nil : MapsToIsLiftable uv (.nil) []
  | cons_true {s: Sort us} (lem: LiftableEmbedding s Univ) {ss: List (Sort us)} (il: Interleaving Univ ss) (req: lem.IsLiftable uv) (bs: List Bool)
        : il.MapsToIsLiftable uv bs → (il.cons lem).MapsToIsLiftable uv (.true::bs)
  | cons_false {s: Sort us} (lem: LiftableEmbedding s Univ) {ss: List (Sort us)} (il: Interleaving Univ ss) (req: ¬lem.IsLiftable uv) (bs: List Bool)
        : il.MapsToIsLiftable uv bs → (il.cons lem).MapsToIsLiftable uv (.false::bs)


namespace MapsToIsLiftable

theorem length_eq_at (uv: Univ) (ss: List (Sort us)) (bs: List Bool) (il: Interleaving Univ ss) (h: il.MapsToIsLiftable uv bs) : il.length = bs.length := by
  dsimp [il.length_def]
  cases ss with
  | nil =>
    cases bs with
    | nil => dsimp
    | cons b bs => rcases h
  | cons s ss =>
    cases bs with
    | nil => rcases h
    | cons b bs =>
      simp
      cases h <;> (
        rename_i il h
        rewrite [← il.length_def]
        exact h.length_eq_at )

variable {il: Interleaving Univ ss} {uv: Univ} in
theorem length_eq {bs: List Bool} (h: il.MapsToIsLiftable uv bs) : il.length = bs.length := h.length_eq_at


theorem bool_list_eq_at (uv: Univ) (ss: List (Sort us)) (il: Interleaving Univ ss) (bs1: List Bool) (h1: il.MapsToIsLiftable uv bs1) (bs2: List Bool) (h2: il.MapsToIsLiftable uv bs2) : bs1 = bs2 := by
  have lm1 := h1.length_eq.symm.trans h2.length_eq
  rcases bs1 with _ | ⟨b1, bs1⟩
  · simp at lm1
    replace lm1 := lm1.symm
    simpa using lm1
  · simp at lm1
    rcases bs2 with _ | ⟨b2, bs2⟩
    · simp at lm1
    · simp at lm1 ⊢
      rcases b1 <;> rcases b2
      · simp only [true_and]
        rcases h1; rename_i il _ h1
        rcases h2; rename_i h2
        exact bool_list_eq_at uv _ il _ h1 _ h2
      · rcases h1; rcases h2
        contradiction
      · rcases h1; rcases h2
        contradiction
      · simp only [true_and]
        rcases h1; rename_i il _ h1
        rcases h2; rename_i h2
        exact bool_list_eq_at uv _ il _ h1 _ h2


variable {il: Interleaving Univ ss} {uv: Univ} in
theorem bool_list_eq {bs1 bs2: List Bool} (h1: il.MapsToIsLiftable uv bs1) (h2: il.MapsToIsLiftable uv bs2) : bs1 = bs2 := bool_list_eq_at _ _ _ _ h1 _ h2



end MapsToIsLiftable

def AnyLiftable (il: Interleaving Univ ss) (uv: Univ) : Prop := ∀⦃bs: List Bool⦄ ⦃_: il.MapsToIsLiftable uv bs⦄, bs.Mem .true

def AllLiftable (il: Interleaving Univ ss) (uv: Univ) : Prop := ∀⦃bs: List Bool⦄ ⦃_: il.MapsToIsLiftable uv bs⦄, bs.Forall (· = .true)

/-
@[ext]
structure Builder (Univ: Sort uu) (len: Nat) (GetSub: (Fin len) → Sort us) where
  getLiftableEmbedding (n: Fin len) : LiftableEmbedding (GetSub n) Univ


namespace Builder


--scoped instance uniqueOfGetSub : Unique ((Fin 0) → Sort us) := Pi.uniqueOfIsEmpty _

def getSub_eq_default (gs: Fin 0 → Sort us) : gs = default := by simp [funext_iff] --(Pi.uniqueOfIsEmpty _).eq_default gs


def nil (Univ: Sort uu) : Builder.{uu, us} Univ 0 default := ⟨(Pi.uniqueOfIsEmpty _).default⟩

@[elab_as_elim]
def recNil.{u}
  {motive: (GetSub: (Fin 0) → Sort us) → (Builder Univ 0 GetSub) → Sort u}
  (nil: motive default (.nil Univ))
  {GetSub: (Fin 0) → Sort us}
  (t: Builder Univ 0 GetSub)
  : motive GetSub t :=
  have lm1: motive GetSub t = motive default (.nil _) := by
    have lm2: GetSub = default := by simp [funext_iff]
    subst lm2
    congr
    rcases t with ⟨t⟩
    dsimp [Builder.nil]
    congr
    simp [funext_iff]
  lm1.mpr nil


def consGetSub (Sub: Sort us) {len: Nat} (GetSub: (Fin len) → Sort us) (i: Fin (len+1)) : Sort us := i.induction Sub (fun i0 _ => GetSub i0)

def cons (Sub: Sort us) (lem: LiftableEmbedding Sub Univ) {len: Nat} {GetSub: (Fin len) → Sort us} (bd: Builder Univ len GetSub) : Builder Univ (len+1) (consGetSub Sub GetSub) where
  getLiftableEmbedding i := i.induction lem (fun i0 _ => bd.getLiftableEmbedding i0)


def tailGetSub {len: Nat} (GetSub: (Fin (len+1)) → Sort us) (i: Fin len) : Sort us := GetSub i.succ

def tail {len: Nat} {Sub: Sort us} {GetSub: (Fin len) → Sort us} (bd: Builder Univ (len+1) (consGetSub Sub GetSub)) : Builder Univ len GetSub where
  getLiftableEmbedding i := bd.getLiftableEmbedding i.succ

--bd0 : Builder Univ (len0 + 1) (consGetSub s0 gs0)

theorem tailGetSub_consGetSub_eq {len: Nat} (GetSub: (Fin (len+1)) → Sort us) : consGetSub (GetSub 0) (tailGetSub GetSub) = GetSub := by
  simp only [funext_iff]
  intro i
  dsimp [consGetSub, tailGetSub]
  cases i using Fin.succRec <;> dsimp


def recConsOnGetSub.{u} {len: Nat}
  {motive: (GetSub: (Fin (len+1)) → Sort us) → Sort u}
  (cons: (Sub: Sort us) → (GetSub: (Fin len) → Sort us) → motive (consGetSub Sub GetSub))
  (t: (Fin (len+1)) → Sort us)
  : motive t :=
  (tailGetSub_consGetSub_eq t).ndrec (cons (t 0) (tailGetSub t))


@[elab_as_elim]
def recNilConsOnGetSub.{u}
  {motive: (len: Nat) → (GetSub: (Fin len) → Sort us) → Sort u}
  (nil: motive 0 default)
  (cons: (Sub: Sort us) → (len: Nat) → (GetSub: (Fin len) → Sort us) → motive len GetSub → motive (len+1) (consGetSub Sub GetSub))
  (len: Nat) (t: (Fin len) → Sort us)
  : motive len t :=
  match len with
  | 0 =>
    have lm1: default = t := by simp [funext_iff]
    lm1.ndrec nil
  | len + 1 =>
    (tailGetSub_consGetSub_eq t).ndrec (cons (t 0) len (tailGetSub t) (recNilConsOnGetSub nil cons len (tailGetSub t)))

section RecNilConsOnGetSub

universe um
variable {m: (len: Nat) → (GetSub: (Fin len) → Sort us) → Sort um}
         {nil0: m 0 default}
         {cons0: (Sub: Sort us) → (len: Nat) → (GetSub: (Fin len) → Sort us) → m len GetSub → m (len+1) (consGetSub Sub GetSub)}


@[defeq]
theorem recNilConsOnGetSub_nil : recNilConsOnGetSub (motive := m) nil0 cons0 0 default = nil0 := by
  dsimp [recNilConsOnGetSub]

@[defeq]
theorem recNilConsOnGetSub_cons {len: Nat} {Sub: Sort us} {t: (Fin len) → Sort us}
  : recNilConsOnGetSub (motive := m) nil0 cons0 (len+1) (consGetSub Sub t) = cons0 Sub len t (recNilConsOnGetSub nil0 cons0 len t) := by
  conv => lhs; dsimp [recNilConsOnGetSub]
  rfl

end RecNilConsOnGetSub

/-
@[elab_as_elim]
def recCons.{u} {len: Nat}
  {motive: (Sub: Sort us) → (GetSub: (Fin len) → Sort us) → (Builder Univ (len+1) (consGetSub Sub GetSub)) → Sort u}
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (GetSub: (Fin len) → Sort us) → (bd: Builder Univ len GetSub) → motive Sub GetSub (Builder.cons Sub lem bd))
  (Sub: Sort us) (GetSub: (Fin len) → Sort us) (t: Builder Univ (len+1) (consGetSub Sub GetSub))
  : motive Sub GetSub t :=
  have lm1: Builder.cons Sub (t.getLiftableEmbedding 0) t.tail = t := by
    dsimp [Builder.cons, tail]
    congr
    simp only [funext_iff]
    intro i
    cases i using Fin.succRec <;> dsimp
  lm1.ndrec (cons Sub (t.getLiftableEmbedding 0) GetSub t.tail)
-/

@[elab_as_elim]
def recNilCons.{u}
  {motive: (len: Nat) → (GetSub: (Fin len) → Sort us) → Builder Univ len GetSub → Sort u}
  (nil: motive 0 default (.nil Univ))
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (GetSub: (Fin len) → Sort us) → (bd: Builder Univ len GetSub) → motive len GetSub bd → motive (len+1) (consGetSub Sub GetSub) (Builder.cons Sub lem bd))
  (len: Nat) (GetSub: (Fin len) → Sort us) (t: Builder Univ len GetSub)
  : motive len GetSub t :=
  recNilConsOnGetSub (motive := fun len0 gs0 => (bd0: Builder Univ len0 gs0) → motive len0 gs0 bd0)
    (fun bd0 => bd0.recNil nil)
    (fun s0 len0 gs0 m0 bd0 =>
      --let bd1 : Builder Univ len0 gs0 := ⟨fun i => bd0.getLiftableEmbedding i.succ⟩
      have lm1: Builder.cons s0 (bd0.getLiftableEmbedding 0) bd0.tail = bd0 := by
        simp [tail]
        rcases bd0 with ⟨bd0⟩
        dsimp [Builder.cons]
        congr
        rw [funext_iff]
        intro i
        cases i using Fin.succRec <;> dsimp
      lm1.ndrec (cons s0 (bd0.getLiftableEmbedding 0) len0 gs0 bd0.tail (m0 bd0.tail))) len GetSub t

section RecNilCons

universe um
variable {m: (len: Nat) → (GetSub: (Fin len) → Sort us) → Builder Univ len GetSub → Sort um}
         {nil0: m 0 default (.nil Univ)}
         {cons0: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (GetSub: (Fin len) → Sort us) → (bd: Builder Univ len GetSub) → m len GetSub bd → m (len+1) (consGetSub Sub GetSub) (Builder.cons Sub lem bd)}

@[defeq]
theorem recNilCons_nil : recNilCons (motive := m) nil0 cons0 0 default (.nil Univ) = nil0 := by
  dsimp [recNilCons, recNilConsOnGetSub, recNil]

--#print List.rec

@[defeq]
theorem recNilCons_cons {s: Sort us} {lem: LiftableEmbedding s Univ} {len: Nat} {gs: (Fin len) → Sort us} {t: Builder Univ len gs} --{t: Builder Univ (len+1) (consGetSub s gs)}
  : recNilCons (motive := m) nil0 cons0 (len+1) (consGetSub s gs) (t.cons s lem) = cons0 s lem len gs t (recNilCons nil0 cons0 len gs t) := by
  dsimp [recNilCons, recNilConsOnGetSub_cons]
  rfl
  --: recNilCons (motive := m) nil0 cons0 (len+1) gs t = cons0 (gs 0)

end RecNilCons

--def toInterleavingAux {len: Nat} {GetSub: (Fin len) → Sort us} (bd: Builder Univ len GetSub) : Interleaving Univ (List.ofFn GetSub) :=
--#check List.ofFnRec



def toInterleaving {len: Nat} {GetSub: (Fin len) → Sort us} (bd: Builder Univ len GetSub) : Interleaving Univ (List.ofFn GetSub) :=
  recNilCons (motive := fun len0 gs0 bd0 => Interleaving Univ (List.ofFn gs0))
    (.nil: Interleaving Univ [])
    (fun Sub lem len0 gs0 bd0 m0 =>
      have lm1: (Sub :: List.ofFn gs0) = (List.ofFn (consGetSub Sub gs0)) := by rw [List.ofFn_succ]; dsimp [consGetSub]
      lm1.ndrec (Interleaving.cons lem m0))
    len GetSub bd


def ofInterleaving {len: Nat} {GetSub: (Fin len) → Sort us} (il: Interleaving Univ (List.ofFn GetSub)) : Builder Univ len GetSub :=
  have lm1: len = il.length := by simp only [length_def, List.length_ofFn]
  ⟨fun i =>
    let i2 : Fin il.length := i.cast lm1
    have lm2: il.GetSub i2 = GetSub i := by
      subst i2
      dsimp [Interleaving.GetSub, subs]
      simp only [List.getElem_ofFn, Fin.eta]
    lm2 ▸ (il.getLiftableEmbedding i2)⟩


/-
theorem ofInterleaving_toInterleaving_leftInverse (len: Nat) (GetSub: (Fin len) → Sort us)
  : Function.LeftInverse ofInterleaving (toInterleaving: Builder Univ len GetSub → Interleaving Univ (List.ofFn GetSub)) := by
  intro bd
  induction len, GetSub, bd using recNilCons with
  | nil =>
    dsimp [nil, ofInterleaving]
    congr
    exact Subsingleton.elim _ _
  | cons s lem len gs bd lm1 =>
    dsimp [ofInterleaving]
    cases len with
    | zero =>
      cases bd using recNil
      conv => rhs; dsimp [cons]
      congr
      simp [funext_iff]
      dsimp [toInterleaving, recNilCons_cons, recNilCons_nil]
      have lm2 := getSub_eq_default (fun a => (default: Sort us))
-/

/-
@[elab_as_elim]
def recNilCons'.{u} --{len: Nat} {GetSub: (Fin len) → Sort us}
  {motive: (len: Nat) → (GetSub: (Fin len) → Sort us) → Builder Univ len GetSub → Sort u}
  (nil: motive 0 default (.nil Univ))
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (GetSub: (Fin len) → Sort us) → (bd: Builder Univ len GetSub) → motive len GetSub bd → motive (len+1) (consGetSub Sub GetSub) (Builder.cons Sub lem bd))
  {len: Nat} {GetSub: (Fin len) → Sort us} (t: Builder Univ len GetSub)
  : motive len GetSub t :=
  recNilCons nil cons len GetSub t
-/

--#check List.equiv
/-
def equivOfToInterleaving {len: Nat} {GetSub: (Fin len) → Sort us} : Builder Univ len GetSub ≃ Interleaving Univ (List.ofFn GetSub) where
  toFun bd := bd.toInterleaving
  invFun il := ofInterleaving il
-/

end Builder
-/

/-
def recNilCons.{u}
  {motive: (len: Nat) → (GetSub: (Fin len) → Sort us) → Builder Univ len GetSub → Sort u}
  (nil: motive 0 default (.nil Univ))
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (GetSub: (Fin len) → Sort us) → (bd: Builder Univ len GetSub) → motive len GetSub bd → motive (len+1) (consGetSub Sub GetSub) (Builder.cons Sub lem bd))
  (len: Nat) (GetSub: (Fin len) → Sort us) (t: Builder Univ len GetSub)
-/




/-
open Builder in
def consOfFn {Sub: Sort us} (lem: LiftableEmbedding Sub Univ) {len: Nat} (GetSub: (Fin len) → Sort us) (il: Interleaving Univ (List.ofFn GetSub)) : Interleaving Univ (List.ofFn (consGetSub Sub GetSub)) :=
  recNilConsOnGetSub (motive := fun len0 gs0 => Interleaving Univ (List.ofFn gs0))
    (.nil)
    (fun s0 len0 gs0 m0 => _)
    len GetSub
-/

/-
def recOfFn.{u}
  {motive: (len: Nat) → (GetSub: (Fin len) → Sort us) → Interleaving Univ (List.ofFn GetSub) → Sort u}
  (nil: motive 0 default .nil)
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (GetSub: (Fin len) → Sort us) → (il: Interleaving Univ (List.ofFn GetSub)) → motive len GetSub il → motive (len+1) (Builder.consGetSub Sub GetSub) )
-/

/-
def toInterleaving {len: Nat} {GetSub: (Fin len) → Sort us} (bd: Builder Univ len GetSub) : Interleaving Univ (List.ofFn GetSub) :=
  recNilCons (motive := fun len0 gs0 bd0 => Interleaving Univ (List.ofFn gs0))
    (.nil: Interleaving Univ [])
    (fun Sub lem len0 gs0 bd0 m0 =>
      have lm1: (Sub :: List.ofFn gs0) = (List.ofFn (consGetSub Sub gs0)) := by rw [List.ofFn_succ]; dsimp [consGetSub]
      lm1.ndrec (Interleaving.cons lem m0))
    len GetSub bd
-/

/-
def toBuilder (il: Interleaving Univ ss) : Builder Univ ss.length (ss.get) where
  getLiftableEmbedding i := il.getLiftableEmbedding i

def ofBuilder (bd: Builder Univ ss.length (ss.get)) : Interleaving Univ ss := (List.ofFn_get ss) ▸ bd.toInterleaving
-/

/-
theorem ofBuilder_toBuilder_leftInverse : Function.LeftInverse (ofBuilder) (toBuilder: Interleaving Univ ss → Builder Univ ss.length (ss.get)) := by
  intro il
  cases il with
  | nil => exact nil_subsingleton.elim _ _
  | cons lem il =>
    rename_i s ss
    generalize (s :: ss) = ss2
-/
    --generalize lm3: (cons lem il).toBuilder = bd
    --generalize lm1: (s :: ss).length = len at lm3
    --generalize lm2: (s :: ss).get = gs

    --let bd2: Builder Univ len gs :=

    --rcases bd with ⟨bd⟩



/-
def equivOfToBuilder : Interleaving Univ ss ≃ Builder Univ ss.length (ss.get) where
  toFun il := il.toBuilder
  invFun bd := ofBuilder bd
-/




structure Builder (Univ: Sort uu) (len: Nat) where
  GetSub (n: Fin len) : Sort us
  getLiftableEmbedding (n: Fin len) : LiftableEmbedding (GetSub n) Univ

namespace Builder


def nil (Univ: Sort uu) : Builder.{uu, us} Univ 0 where
  GetSub n := n.elim0
  getLiftableEmbedding n := n.elim0

instance zero_subsingleton : Subsingleton (Builder Univ 0) where
  allEq := by
    rintro ⟨gs1, gl1⟩ ⟨gs2, gl2⟩
    have lm1: gs1 = gs2 := by simp [funext_iff]
    subst lm1
    simp [funext_iff]


def cons (Sub: Sort us) (lem: LiftableEmbedding Sub Univ) {len: Nat} (bd: Builder Univ len) : Builder Univ (len+1) :=
  let getSub (n: Fin (len + 1)) : Sort us := n.induction Sub (fun n0 _ => bd.GetSub n0)
  have lm1 : getSub 0 = Sub := Fin.induction_zero _ _
  {
    GetSub := getSub
    getLiftableEmbedding (n: Fin (len + 1)) :=
      n.induction (motive := fun n0 => LiftableEmbedding (getSub n0) Univ)
                  (lm1.symm ▸ lem)
                  (fun n0 _ =>
                    have lm2: bd.GetSub n0 = getSub (n0.succ) := by subst getSub; simp only [Fin.induction_succ]
                    lm2 ▸ (bd.getLiftableEmbedding n0))
  }


def tail {len: Nat} (bd: Builder Univ (len+1)) : Builder Univ len where
  GetSub n := bd.GetSub n.succ
  getLiftableEmbedding n := bd.getLiftableEmbedding n.succ

@[elab_as_elim]
def recCons.{u} {len: Nat}
  {motive: Builder Univ (len+1) → Sort u}
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (bd: Builder Univ len) → motive (.cons Sub lem bd))
  (t: Builder Univ (len+1))
  : motive t :=
    let Sub : Sort us := t.GetSub 0
    let lem : LiftableEmbedding Sub Univ := t.getLiftableEmbedding 0
    have lm1: Builder.cons Sub lem t.tail = t := by
      subst Sub lem
      rcases t with ⟨gs, gl⟩
      dsimp [Builder.cons, Builder.tail]
      simp
      refine (And.intro ?_ ?_)
      · simp [funext_iff]
        intro n0
        cases n0 using Fin.succRec <;> dsimp
      · refine Function.hfunext (Eq.refl _) ?_
        intro n1 n2 lm1
        rewrite [heq_eq_eq] at lm1
        subst lm1
        cases n1 using Fin.succRec <;> (dsimp; rfl)
    lm1.ndrec (cons Sub lem t.tail)

@[elab_as_elim]
def recNilCons.{u}
  {motive : (len: Nat) → Builder Univ len → Sort u}
  (nil: motive 0 (.nil Univ))
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (bd: Builder Univ len) → motive (len+1) (.cons Sub lem bd))
  {len: Nat} (t: Builder Univ len)
  : motive len t :=
  match len with
  | 0 =>
    have lm1: Builder.nil Univ = t := zero_subsingleton.elim _ _
    lm1.ndrec nil
  | len + 1 =>
    t.recCons (fun Sub lem bd => cons Sub lem len bd)


def toInterleavingAt (len: Nat) (bd: Builder Univ len) : Interleaving Univ (List.ofFn bd.GetSub) :=
  match len, bd with
  | 0, _ => (.nil: Interleaving Univ [])
  | len+1, bd2 => bd2.recCons (fun Sub lem bd0 =>
      have lm1: Sub :: List.ofFn bd0.GetSub = List.ofFn (bd0.cons Sub lem).GetSub := by simp [cons]
      lm1.ndrec (Interleaving.cons lem (toInterleavingAt len bd0)))

def toInterleaving {len: Nat} (bd: Builder Univ len) : Interleaving Univ (List.ofFn bd.GetSub) := bd.toInterleavingAt len

def toInterleavingSigma {len: Nat} (bd: Builder Univ len) : (ss: List (Sort us)) ×' (Interleaving Univ ss) := ⟨List.ofFn bd.GetSub, bd.toInterleaving⟩


def ofInterleaving (il: Interleaving Univ ss) : Builder Univ il.length where
  GetSub := il.GetSub
  getLiftableEmbedding := il.getLiftableEmbedding

def ofInterleavingSigma (ils: (ss: List (Sort us)) ×' (Interleaving Univ ss)) : Builder Univ ils.snd.length := ofInterleaving ils.snd

end Builder


end Interleaving

/-
inductive IsLiftableVector (rv: R) : (bs: List (LeftTypeBundled.{ur, ul} R)) → (Interleaving R bs) → List Bool → Prop where
  | nil : IsLiftableVector rv [] (Interleaving.nil) []
  | cons_true (b: LeftTypeBundled R) (bs: List (LeftTypeBundled R)) (il: Interleaving R bs)
              (b2: b.liftableEmbedding.IsLiftable rv) (bs2: List Bool)
        : IsLiftableVector rv bs il bs2 → IsLiftableVector rv (b::bs) (il.cons b) (.true::bs2)
  | cons_false (b: LeftTypeBundled R) (bs: List (LeftTypeBundled R)) (il: Interleaving R bs)
               (b2: ¬b.liftableEmbedding.IsLiftable rv) (bs2: List Bool)
        : IsLiftableVector rv bs il bs2 → IsLiftableVector rv (b::bs) (il.cons b) (.false::bs2)



structure LeftTypeBundled.{ur, ul} (R: Type ur) where
  L: Type ul
  liftableEmbedding: LiftableEmbedding L R

namespace LeftTypeBundled

def ofLiftableEmbedding {L R: Type*} (lem: LiftableEmbedding L R) : LeftTypeBundled R := .mk L lem

end LeftTypeBundled


inductive Interleaving.{ur, ul} (R: Type ur) : List (LeftTypeBundled.{ur, ul} R) → Type _ where
  | nil : Interleaving R []
  | cons (b: LeftTypeBundled R) (bs: List (LeftTypeBundled R)) : (Interleaving R bs) → (Interleaving R (b::bs))

namespace Interleaving

universe ur ul

variable {R: Type ur}


end Interleaving
-/



end Nemonuri.Functions.LiftableEmbedding

end
