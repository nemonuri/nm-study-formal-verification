module

public import Nemonuri.Functions.LiftableEmbedding.Interleaving.IsLiftableIndex

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding.Interleaving

universe uu us
variable {Univ: Sort uu}


inductive MapsTo (il: Interleaving Univ) (uv: Univ) {α: Type*} (f: SubBundled Univ → α) (as: List α) : Prop where
  | intro (req: il.mapSubBundled f = as)


namespace MapsTo

variable {il: Interleaving Univ} {uv: Univ} {α: Type*} (f: SubBundled Univ → α) {as: List α}

theorem length_eq (h: il.MapsTo uv f as) : il.length = as.length := by
  rcases h with ⟨lm1⟩
  rewrite [Eq.comm] at lm1
  subst lm1
  symm
  exact mapSubBundled_length_eq


theorem map_eq_iff_getElem_eq (h: il.MapsTo uv f as) {n: Nat} {req: n < as.length} {a: α}
  : (f (il.getSubBundled ⟨n, h.length_eq.symm ▸ req⟩) = a) ↔ (as[n] = a) := by
  rcases h with ⟨lm1⟩
  have lm1_1 := lm1.symm
  subst lm1_1
  revert lm1
  simp
  dsimp only [GetElem.getElem]
  rw [mapSubBundled_get_eq]


end MapsTo

structure MapsAt (il: Interleaving Univ) (uv: Univ) {α: Type*} (f: SubBundled Univ → α) (n: Nat) (a: α) : Prop where
  lt_length: n < il.length
  map_eq: f (il.getSubBundled ⟨n, lt_length⟩) = a


inductive MapsToIsLiftable (il: Interleaving Univ) (uv: Univ) (bs: List Bool) : Prop where
  | intro (req: il.mapSubBundled (fun sb => (decide (sb.liftableEmbedding.IsLiftable uv))) = bs)

namespace MapsToIsLiftable

variable {il: Interleaving Univ} {uv: Univ} {bs: List Bool}

theorem length_eq (h: il.MapsToIsLiftable uv bs) : il.length = bs.length := by
  rcases h with ⟨lm1⟩
  rewrite [Eq.comm] at lm1
  subst lm1
  symm
  exact mapSubBundled_length_eq

attribute [- simp] List.get_eq_getElem in
theorem get_eq_true_iff_isLiftableIndex (h: il.MapsToIsLiftable uv bs) {i: Fin il.length}
  : (bs.get (i.cast h.length_eq) = .true) ↔ il.IsLiftableIndex uv i := by
  rcases h with ⟨lm1⟩
  have lm1_1 := lm1.symm
  subst lm1_1
  revert lm1
  simp
  rcases i with ⟨i, lm1⟩
  dsimp
  rw [mapSubBundled_get_eq] <;> try assumption
  simp
  dsimp [getLiftableEmbedding, IsLiftableIndex]
  exact Iff.rfl

end MapsToIsLiftable

def MapsToSub (il: Interleaving Univ) (uv: Univ) (subs: List (Sort us)) : Prop := il.MapsTo uv SubBundled.Sub subs

@[defeq]
theorem mapsToSub_def {il: Interleaving Univ} {uv: Univ} {subs: List (Sort us)} : il.MapsToSub uv subs = il.MapsTo uv SubBundled.Sub subs := rfl

def MapsSubAt (il: Interleaving Univ) (uv: Univ) (n: Nat) (Sub: Sort us) : Prop := il.MapsAt uv SubBundled.Sub n Sub

namespace MapsSubAt

variable {il: Interleaving Univ} {uv: Univ} {n: Nat} {Sub: Sort us}

theorem sub_eq (h: il.MapsSubAt uv n Sub) : il.getSub ⟨n, h.lt_length⟩ = Sub := by
  dsimp [MapsSubAt] at h
  rcases h with ⟨lm1, lm2⟩
  have lm2_1 := lm2.symm
  subst lm2_1
  dsimp [getSub]

def equiv (h: il.MapsSubAt uv n Sub) : il.getSub ⟨n, h.lt_length⟩ ≃ Sub := Equiv.cast h.sub_eq



end MapsSubAt

/-
inductive MapsToSub (il: Interleaving Univ) (uv: Univ) (subs: List (Sort us)) : Prop where
  | intro (req: il.mapSubBundled (SubBundled.Sub) = subs)
-/

--def IsUniverseEqUnion

--def IsLiftableExists (il: Interleaving Univ) (uv: Univ) : Prop := ∃(i: Fin il.length), (il.getLiftableEmbedding i).IsLiftable uv



--def IsLiftableAll

/-
inductive CanLiftToAny (il: Interleaving Univ) (uv: Univ) : Prop where
  | intro (bs: )
-/

end Nemonuri.Functions.LiftableEmbedding.Interleaving

end
