module

public import Nemonuri.Relations.Heterogeneous.SumRelGen.IsSubIntersection

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

variable {αl αr: Type*} --{rel: αl → αr → Prop}

namespace SumUnion

def SetLikeHEq (rel: αl → αr → Prop) (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] (sal: Sαl) (sar: Sαr) : Prop := SetHEq rel sal sar

variable {rel: αl → αr → Prop} {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr}

@[defeq]
theorem setLikeHEq_def : SetLikeHEq rel Sαl Sαr sal sar = SetHEq rel ↑sal ↑sar := rfl

namespace SetLikeHEq

theorem of_setHEq (rel: αl → αr → Prop) (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr} (req: SetHEq rel ↑sal ↑sar) : SetLikeHEq rel Sαl Sαr sal sar := req

theorem leftUnique_of (rel: αl → αr → Prop) [IsBiUnique rel] (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : Relator.LeftUnique (SetLikeHEq rel Sαl Sαr) := by
  intro sl1 sl2 sr lm1 lm2
  dsimp [setLikeHEq_def] at lm1 lm2
  have lm3 := SetHEq.leftUnique_of_rel rel lm1 lm2
  simpa using lm3

theorem rightUnique_of (rel: αl → αr → Prop) [IsBiUnique rel] (Sαl Sαr: Type*) [SetLike Sαl αl] [SetLike Sαr αr] : Relator.RightUnique (SetLikeHEq rel Sαl Sαr) := by
  intro sl sr1 sr2 lm1 lm2
  dsimp [setLikeHEq_def] at lm1 lm2
  have lm3 := SetHEq.rightUnique_of_rel rel lm1 lm2
  simpa using lm3


variable [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr]

theorem projectLeftSetToRightSet_eq {sal: Sαl} {sar: Sαr} (h: SetLikeHEq rel Sαl Sαr ↑sal ↑sar) : projectLeftSetToRightSet rel ↑sal = ↑sar := by
  dsimp [setLikeHEq_def] at h
  exact h.projectLeftSetToRightSet_eq

theorem projectRightSetToLeftSet_eq {sal: Sαl} {sar: Sαr} (h: SetLikeHEq rel Sαl Sαr ↑sal ↑sar) : projectRightSetToLeftSet rel ↑sar = ↑sal := by
  dsimp [setLikeHEq_def] at h
  exact h.projectRightSetToLeftSet_eq


end SetLikeHEq

theorem setLikeHEq_iff_eq_and_eq [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr}
  : (SetLikeHEq rel Sαl Sαr ↑sal ↑sar) ↔ (projectLeftSetToRightSet rel ↑sal = ↑sar ∧ projectRightSetToLeftSet rel ↑sar = ↑sal) := by
  simp only [setLikeHEq_def, setHEq_iff_eq_and_eq]

/-
theorem setLikeHEq_iff [IsBiUnique rel] {Sαl Sαr: Type*} [SetLike Sαl αl] [SetLike Sαr αr] {sal: Sαl} {sar: Sαr}
  : (SetLikeHEq rel Sαl Sαr ↑sal ↑sar) := by
  dsimp [setLikeHEq_def, setHEq_def]
  simp [Set.ext_iff]
  intro su
  simp [setOfLeftSet, setOfRightSet]
-/

end SumUnion



end Nemonuri.Relations.Heterogeneous

end
