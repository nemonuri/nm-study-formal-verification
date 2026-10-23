module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.SetLikeHEq

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} {rel: αl → αr → Prop}

namespace SumUnion

namespace SetHEq

protected instance isBiUnique (rel: αl → αr → Prop) [IsBiUnique rel] : IsBiUnique (SetHEq rel) where
  biUnique := ⟨leftUnique_of_rel rel, rightUnique_of_rel rel⟩

end SetHEq

namespace SetLikeHEq

protected instance isBiUnique (rel: αl → αr → Prop) [IsBiUnique rel] (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : IsBiUnique (SetLikeHEq rel Sαl Sαr) where
  biUnique := ⟨leftUnique_of rel Sαl Sαr, rightUnique_of rel Sαl Sαr⟩

end SetLikeHEq

namespace IsSubIntersection

section SetSection

variable [IsBiUnique rel] [HasPartialCongruence (SetHEq rel)]


theorem setHEq_rightOfRel?_eq_some_projectLeftSetToRightSet {sl: Set αl} (h: IsSubIntersection (setOfLeftSet rel sl))
  : HasPartialCongruence.rightOfRel? (SetHEq rel) sl = .some (projectLeftSetToRightSet rel sl) := by
  rw [HasPartialCongruence.rightOfRel?_eq_some_iff_rel]
  exact SetHEq.of_isSubIntersection_left h

theorem setHEq_leftOfRel?_eq_some_projectRightSetToLeftSet {sr: Set αr} (h: IsSubIntersection (setOfRightSet rel sr))
  : HasPartialCongruence.leftOfRel? (SetHEq rel) sr = .some (projectRightSetToLeftSet rel sr) := by
  rw [HasPartialCongruence.leftOfRel?_eq_some_iff_rel]
  exact SetHEq.of_isSubIntersection_right h

end SetSection

variable {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] [HasPartialCongruence (SetLikeHEq rel Sαl Sαr)]

/-
theorem setLikeHEq_rightOfRel?_eq_some_projectLeftSetToRightSet {sal: Sαl} (h: IsSubIntersection (setOfLeftSet rel ↑sal))
  : (HasPartialCongruence.rightOfRel? (SetLikeHEq rel Sαl Sαr) sal).map (SetLike.coe) = .some (projectLeftSetToRightSet rel ↑sal) := by
-/


end IsSubIntersection






--def isSetHEq {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr]


end SumUnion


end Nemonuri.Relations.Heterogeneous

end
