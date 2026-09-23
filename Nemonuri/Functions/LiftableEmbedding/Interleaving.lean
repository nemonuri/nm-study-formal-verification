module

public import Nemonuri.Functions.LiftableEmbedding.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding


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

inductive IsLiftableVector (rv: R) : (bs: List (LeftTypeBundled.{ur, ul} R)) → (Interleaving R bs) → List Bool → Prop where
  | nil : IsLiftableVector rv [] (Interleaving.nil) []
  | cons_true (b: LeftTypeBundled R) (bs: List (LeftTypeBundled R)) (il: Interleaving R bs)
              (b2: b.liftableEmbedding.IsLiftable rv) (bs2: List Bool)
        : IsLiftableVector rv bs il bs2 → IsLiftableVector rv (b::bs) (il.cons b) (.true::bs2)
  | cons_false (b: LeftTypeBundled R) (bs: List (LeftTypeBundled R)) (il: Interleaving R bs)
               (b2: ¬b.liftableEmbedding.IsLiftable rv) (bs2: List Bool)
        : IsLiftableVector rv bs il bs2 → IsLiftableVector rv (b::bs) (il.cons b) (.false::bs2)


end Interleaving




end Nemonuri.Functions.LiftableEmbedding

end
