module

public import Nemonuri.Functions.LiftableEmbedding.Interleaving.Basic
public import Mathlib.Data.Vector.Basic

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Functions.LiftableEmbedding.Interleaving

universe uu us

def LengthIndexed (Univ: Sort uu) (len: Nat) : Type (max uu us) := List.Vector ((SubBundled.{uu+1, us} (PLift.{uu} Univ))) len

@[defeq]
theorem lengthIndexed_def {Univ: Sort uu} {len: Nat} : LengthIndexed Univ len = List.Vector ((SubBundled (PLift Univ))) len := rfl

namespace LengthIndexed

variable {Univ: Sort uu} {len: Nat}

def toBasic (ill: LengthIndexed Univ len) : Interleaving Univ := ill.toList


end LengthIndexed


end Nemonuri.Functions.LiftableEmbedding.Interleaving
