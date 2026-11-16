module



@[expose] public section


set_option autoImplicit false

namespace Nemonuri.TypeLists

inductive IterNonempty.{u} : List (Type u) → Prop where
  | nil : IterNonempty []
  | cons (Head: Type u) (tail: List (Type u)) (v: Head) (req: IterNonempty tail) : IterNonempty (Head::tail)

namespace IterNonempty

universe u

theorem nonempty_head (Head: Type u) (tail: List (Type u)) (h: IterNonempty (Head::tail)) : Nonempty Head := by
  rcases h with _ | ⟨_,_,v,_⟩
  exact ⟨v⟩

theorem nonempty_mem {tys: List (Type u)} (h: IterNonempty tys) (Ty: Type u) (req: Ty ∈ tys) : Nonempty Ty := by
  rcases h with _ | ⟨_,_,v,h⟩
  · simp at req
  · simp at req
    rcases req with lm1 | lm1
    · subst lm1
      exact ⟨v⟩
    · exact h.nonempty_mem Ty lm1

theorem nonempty_fin {tys: List (Type u)} (h: IterNonempty tys) (i: Fin tys.length) : Nonempty tys[i] := by
  rcases h with _ | ⟨_,_,v,h⟩
  · exact i.elim0
  · rcases i with ⟨i, lm1⟩
    simp at lm1
    rcases i with _ | ⟨i⟩
    · dsimp
      exact ⟨v⟩
    · simp at lm1 ⊢
      exact h.nonempty_fin ⟨i, lm1⟩


end IterNonempty


class HasIterNonempty.{u} (tys: List (Type u)) : Prop where
  iterNonempty: IterNonempty tys


end Nemonuri.TypeLists

end
