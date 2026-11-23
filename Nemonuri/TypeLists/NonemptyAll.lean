module



@[expose] public section


set_option autoImplicit false

namespace Nemonuri.TypeLists

inductive NonemptyAll.{u} : List (Type u) → Prop where
  | nil : NonemptyAll []
  | cons (Head: Type u) (tail: List (Type u)) (v: Head) (req: NonemptyAll tail) : NonemptyAll (Head::tail)

namespace NonemptyAll

universe u

theorem nonempty_head (Head: Type u) (tail: List (Type u)) (h: NonemptyAll (Head::tail)) : Nonempty Head := by
  rcases h with _ | ⟨_,_,v,_⟩
  exact ⟨v⟩

theorem nonempty_mem {tys: List (Type u)} (h: NonemptyAll tys) (Ty: Type u) (req: Ty ∈ tys) : Nonempty Ty := by
  rcases h with _ | ⟨_,_,v,h⟩
  · simp at req
  · simp at req
    rcases req with lm1 | lm1
    · subst lm1
      exact ⟨v⟩
    · exact h.nonempty_mem Ty lm1

theorem nonempty_fin {tys: List (Type u)} (h: NonemptyAll tys) (i: Fin tys.length) : Nonempty tys[i] := by
  rcases h with _ | ⟨_,_,v,h⟩
  · exact i.elim0
  · rcases i with ⟨i, lm1⟩
    simp at lm1
    rcases i with _ | ⟨i⟩
    · dsimp
      exact ⟨v⟩
    · simp at lm1 ⊢
      exact h.nonempty_fin ⟨i, lm1⟩


end NonemptyAll


class HasNonemptyAll.{u} (tys: List (Type u)) : Prop where
  NonemptyAll: NonemptyAll tys


end Nemonuri.TypeLists

end
