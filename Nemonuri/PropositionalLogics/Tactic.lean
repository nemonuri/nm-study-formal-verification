module

public meta import Nemonuri.PropositionalLogics.Attributes
public import Nemonuri.PropositionalLogics.Basic

@[expose] public section

namespace Nemonuri.PropositionalLogics

namespace SatRel.IsSat

attribute [pl_simp] true_intro atom_iff neg_iff false_iff and_iff or_iff imp_iff_imp

end SatRel.IsSat

attribute [pl_simp] EvalLike.toIndicator_def

attribute [pl_simp low] Indicator.mk_fn_eq Indicator.mk_eq

end Nemonuri.PropositionalLogics

end
