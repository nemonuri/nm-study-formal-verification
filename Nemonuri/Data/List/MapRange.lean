module

@[expose] public section

set_option autoImplicit false

namespace List

universe u u2


theorem range_eq_cons_range'_1 (n: Nat) : List.range (n + 1) = (0::(List.range' 1 n)) := by
  simp [List.range_eq_range']
  dsimp [List.range']

variable {β: Type u2}

theorem range'_pmap_congr (start1 start2 len: Nat) (Rel: Nat → Nat → Prop)
  (f1: (n: Nat) → Rel start1 n → β) (f2: (n: Nat) → Rel start2 n → β)
  (req1: (n: Nat) → (n ∈ List.range' start1 len) → Rel start1 n)
  (req2: (n: Nat) → (n ∈ List.range' start2 len) → Rel start2 n)
  (req3: (idx: Nat) → (req_idx: idx < len) → (f1 (start1 + idx) (req1 _ (by simpa)) = f2 (start2 + idx) (req2 _ (by simpa))) )
  : (List.range' start1 len).pmap f1 req1 = (List.range' start2 len).pmap f2 req2 := by
  have (eq := lm2) lenProxy := len
  rcases len with _ | ⟨len⟩
  · dsimp
  · simp [range'_1_concat]
    refine ⟨?_, ?_⟩
    · refine range'_pmap_congr start1 start2 len Rel f1 f2 _ _ ?_
      intro idx lm1
      refine req3 idx ?_
      apply Nat.lt_add_right
      exact lm1
    · refine req3 len ?_
      exact Nat.lt_add_one _




/-
  induction len with
  | zero => simp only [range'_zero, pmap_nil]
  | succ len lm1 =>
    simp [range'_1_concat]
    refine ⟨?_, ?_⟩
    ·
-/

end List

end
