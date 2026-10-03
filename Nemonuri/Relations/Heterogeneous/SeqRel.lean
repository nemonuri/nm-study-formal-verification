module

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe u1 u2

variable {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2}

inductive SeqRel (piRel: ((x: α1) → (β1 x)) → ((x: α2) → (β2 x)) → Prop) (domRel: α1 → α2 → Prop) : (x1: α1) → (x2: α2) → (β1 x1) → (β2 x2) → Prop where
  | intro (pi1: (x: α1) → (β1 x)) (pi2: (x: α2) → (β2 x)) (req1: piRel pi1 pi2) (x1: α1) (x2: α2) (req2: domRel x1 x2) :
          SeqRel piRel domRel x1 x2 (pi1 x1) (pi2 x2)


end Nemonuri.Relations.Heterogeneous

end
