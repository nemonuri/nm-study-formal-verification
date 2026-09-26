module

public import Nemonuri.Functions.LiftableEmbedding.Basic

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

structure Builder (Univ: Sort uu) (len: Nat) (GetSub: (Fin len) → Sort us) where
  getLiftableEmbedding (n: Fin len) : LiftableEmbedding (GetSub n) Univ


namespace Builder


scoped instance uniqueOfGetSub : Unique ((Fin 0) → Sort us) := Pi.uniqueOfIsEmpty _

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

def tail {len: Nat} {GetSub: (Fin (len+1)) → Sort us} (bd: Builder Univ (len+1) GetSub) : Builder Univ len (tailGetSub GetSub) where
  getLiftableEmbedding i := bd.getLiftableEmbedding i.succ


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

#print Nat.rec
#print List.rec

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


def recNilCons.{u} --{len: Nat} {GetSub: (Fin len) → Sort us}
  {motive: (len: Nat) → (GetSub: (Fin len) → Sort us) → Builder Univ len GetSub → Sort u}
  (nil: motive 0 default (.nil Univ))
  (cons: (Sub: Sort us) → (lem: LiftableEmbedding Sub Univ) → (len: Nat) → (GetSub: (Fin len) → Sort us) → (bd: Builder Univ len GetSub) → motive len GetSub bd → motive (len+1) (consGetSub Sub GetSub) (Builder.cons Sub lem bd))
  (len: Nat) (GetSub: (Fin len) → Sort us) (t: Builder Univ len GetSub)
  : motive len GetSub t :=
  recNilConsOnGetSub (motive := fun len0 gs0 => (bd0: Builder Univ len0 gs0) → motive len0 gs0 bd0)
    (fun bd0 => bd0.recNil nil)
    (fun s0 len0 gs0 m0 bd0 =>
      let bd1 : Builder Univ len0 gs0 := ⟨fun i => bd0.getLiftableEmbedding i.succ⟩
      have lm1: Builder.cons s0 (bd0.getLiftableEmbedding 0) bd1 = bd0 := by
        subst bd1
        rcases bd0 with ⟨bd0⟩
        dsimp [Builder.cons]
        congr
        rw [funext_iff]
        intro i
        cases i using Fin.succRec <;> dsimp
      lm1.ndrec (cons s0 (bd0.getLiftableEmbedding 0) len0 gs0 bd1 (m0 bd1))) len GetSub t

#print recNilCons





/-
def toInterleavingAt (len: Nat) (GetSub: (Fin len) → Sort us) (bd: Builder Univ len GetSub) : Interleaving Univ (List.ofFn GetSub) :=
  match len with
  | 0 => bd.recNil (.nil: Interleaving Univ [])
  | len+1 =>
    have lm1 := tailGetSub_consGetSub_eq GetSub |>.symm
    let bd2 := lm1.ndrec bd
    let aux cons0 : Interleaving Univ (List.ofFn GetSub) := recCons cons0 (GetSub 0) (tailGetSub GetSub) bd2
    aux (fun Sub lem GetSub0 bd0 =>
        have lm2: Sub :: List.ofFn GetSub0 = List.ofFn GetSub := by
        lm2.ndrec (Interleaving.cons lem (toInterleavingAt len GetSub0 bd0))
      )
-/
/-

-/
    --recCons (Univ := Univ) (len := len) (fun Sub lem GetSub0 bd0 => Interleaving.cons lem (toInterleavingAt len GetSub0 bd0) ) (GetSub 0) (tailGetSub GetSub) (lm1.ndrec bd)


/-
def recCons'.{u} {len: Nat} {GetSub: (Fin (len+1)) → Sort us}
  {motive: Builder Univ (len+1) GetSub → Sort u}
  (cons: (lem: LiftableEmbedding (GetSub 0) Univ) → (bd: Builder Univ len (tailGetSub GetSub)) → motive (tailGetSub_consGetSub_eq.ndrec (.cons (GetSub 0) lem bd)))
  (t: Builder Univ (len+1) GetSub)
  : motive t :=
  let aux lm1 : motive t := Eq.ndrec (motive := fun x => motive x) (cons (t.getLiftableEmbedding 0) t.tail) lm1
  aux (by
    refine eq_of_heq ?_
    symm
    rw [heq_eqRec_iff_heq]
    rcases t with ⟨t⟩
    dsimp [Builder.cons, tail]
    have lm2 := @tailGetSub_consGetSub_eq len GetSub
    suffices goal: t = (fun i => Fin.induction (t 0) (fun i0 x => t i0.succ) i) from by
      conv => lhs; rw [goal]
      have := heq_of
  )
-/


    --refine heq

/-
    rcases t with ⟨t⟩
    dsimp [Builder.cons, tail]
    have lm2 := @tailGetSub_consGetSub_eq len GetSub
    refine eq_of_heq ?_
    refine eqRec_heq_self ?_ ?_
-/
    --have := eqre

    --

/-
    rcases t with ⟨t⟩
    dsimp [Builder.cons, tail]
    have := eqRec_heq
      --simp only [funext_iff] at goal
-/
/-
    conv =>
      lhs
      arg @-2
-/
    --dsimp [Builder.cons, tail]

  --let lem : LiftableEmbedding (GetSub 0) Univ := t.getLiftableEmbedding 0
  --have








end Builder

/-
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


def ofInterleaving (il: Interleaving Univ ss) : Builder Univ il.length where
  GetSub := il.GetSub
  getLiftableEmbedding := il.getLiftableEmbedding


end Builder
-/

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
