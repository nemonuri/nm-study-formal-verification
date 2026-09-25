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
