module

public import Nemonuri.Executions.ExecutionFragment.Basic

@[expose] public section

namespace Nemonuri.TransitionSystem

namespace ExecutionFragmentRaw



variable {ts: TransitionSystem} {raw: ts.ExecutionFragmentRaw}

theorem IsPrefix.lt_aux {n1 n2: Nat} {en: ENat} (h1: n1 < n2) (h2: Nat.cast n2 < en) : Nat.cast n1 < en :=
  calc
    _ < _ := ENat.coe_lt_coe.mpr h1
    _ < _ := h2


structure IsPrefix (raw: ts.ExecutionFragmentRaw) (pf: ts.FiniteExecutionFragmentRaw) : Prop where
  states_length_lt: pf.states.length < raw.states.length?
  states_prefix (i: Nat) (req: i < pf.states.length) : (pf.states[i]'(req)) = (raw.states[i]'(IsPrefix.lt_aux req states_length_lt))
  actions_length_lt: pf.actions.length < raw.actions.length?
  actions_prefix (i: Nat) (req: i < pf.actions.length) : (pf.actions[i]'(req)) = (raw.actions[i]'(IsPrefix.lt_aux req actions_length_lt))


theorem _root_.Nat.gt_imp_pos {n1 n2: Nat} (h: n1 < n2) : 0 < n2 := by
  induction n1 with
  | zero => exact h
  | succ n _ =>
    calc
      0 < 1 := Nat.zero_lt_one
      _ ≤ _ := Nat.le_add_left _ n
      _ < _ := h


theorem IsPostfix.lt_aux {n: Nat} {m: ENat} {i: Nat} (req1: i < n) (req2: n < m.toNat)
  : (m.toNat - n + i) < m :=
  calc
    m ≥ m.toNat := m.coe_toNat_le_self
    _ > Nat.cast (m.toNat - (n - i)) := Nat.sub_lt (Nat.gt_imp_pos req2) (Nat.zero_lt_sub_of_lt req1) |> ENat.coe_lt_coe.mpr
    _ = Nat.cast (m.toNat - n + i) := ENat.coe_inj.mpr (by omega)


structure IsPostfix (raw: ts.ExecutionFragmentRaw) (pf: ts.FiniteExecutionFragmentRaw) : Prop where
  states_length_lt: pf.states.length < raw.states.length?.toNat
  states_postfix (i: Nat) (req: i < pf.states.length) :
    (pf.states[i]'(req)) = (raw.states[raw.states.length?.toNat - pf.states.length + i]'(IsPostfix.lt_aux req states_length_lt))
  actions_length_lt: pf.actions.length < raw.actions.length?.toNat
  actions_postfix (i: Nat) (req: i < pf.actions.length) :
    (pf.actions[i]'(req)) = (raw.actions[raw.actions.length?.toNat - pf.actions.length + i]'(IsPostfix.lt_aux req actions_length_lt))

@[simp]
theorem infinite_not_isPostfix {ρ} {pf} : ¬(@ExecutionFragmentRaw.infinite ts ρ).IsPostfix pf := by
  intro lm1
  have lm2 := lm1.states_length_lt
  simp at lm2

theorem isPostfix_imp_isFinite {pf} (h: raw.IsPostfix pf) : raw.isFinite := by
  cases raw
  · simp
  · simp at h

structure ArePrefixAndPostfix (raw: ts.ExecutionFragmentRaw) (pref: ts.FiniteExecutionFragmentRaw) (postf: ts.FiniteExecutionFragmentRaw) : Prop where
  is_prefix: raw.IsPrefix pref
  is_postfix: raw.IsPostfix postf
  states_not_overlap: pref.states.length + postf.states.length ≤ raw.states.length?.toNat
  actions_not_overlap: pref.actions.length + postf.actions.length ≤ raw.actions.length?.toNat

@[simp]
theorem infinite_not_arePrefixAndPostfix {ρ pref postf} : ¬(@ExecutionFragmentRaw.infinite ts ρ).ArePrefixAndPostfix pref postf := by
  intro lm1
  have lm2 := lm1.is_postfix
  simp at lm2

theorem arePrefixAndPostfix_imp_isFinite {pref postf} (h: raw.ArePrefixAndPostfix pref postf) : raw.isFinite := h.is_postfix |> isPostfix_imp_isFinite


end ExecutionFragmentRaw

end Nemonuri.TransitionSystem

end
