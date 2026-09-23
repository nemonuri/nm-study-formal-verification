module

public meta import Nemonuri.Functions.Attributes

@[expose] public section

set_option autoImplicit false

namespace Nemonuri

namespace SimpLemmas

universe u1 u2

@[range_mem_simp, lift_to_left_norm]
theorem exists_apply_eq_iff {L: Sort u1} {R: Sort u2} {f: L → R} {rv: R}
  : (∃(lv: L), f lv = rv) ↔ (∃(lv: L), rv = f lv) := by
  constructor
  · rintro ⟨lv, lm1⟩
    rewrite [Eq.comm] at lm1
    subst lm1
    exists lv
  · rintro ⟨lv, lm1⟩
    subst lm1
    exists lv


end SimpLemmas

end Nemonuri

end
