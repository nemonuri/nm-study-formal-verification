module

public import Nemonuri.Functions.LiftableEmbedding.Interleaving.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding.Interleaving

universe uu us
variable {Univ: Sort uu}


def IsLiftableIndex (il: Interleaving Univ) (uv: Univ) (i: Fin il.length) : Prop := (il.getLiftableEmbedding i).IsLiftable uv

--theorem isLiftableIndex_def {il: Interleaving Univ} {uv: Univ} {i: Fin il.length}

inductive IsInLiftableUnion (il: Interleaving Univ) (uv: Univ) : Prop where
  | intro (n: Nat) (req1: n < il.length) (req2: il.IsLiftableIndex uv ⟨n, req1⟩)

def IsUniverseLiftableUnion (il: Interleaving Univ) : Prop := ∀⦃uv: Univ⦄, il.IsInLiftableUnion uv



end Nemonuri.Functions.LiftableEmbedding.Interleaving

end
