module

public import Nemonuri.Executions.Basic
--public import Nemonuri.SequenceProdLike.ListProd

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem


structure ExecutionFragment (ts: TransitionSystem) extends toSequenceProd: SequenceProd ts.S ts.Act where
  valid: IsExecutionFragment toSequenceProd

/-
structure ExecutionFragmentLike (ts: TransitionSystem) (SP: Type*) [SequenceProdLike SP ts.S ts.Act] where
  sequenceProdLike: SP
  valid: ts.IsExecutionFragment sequenceProdLike

open SequenceProdLike in
abbrev FiniteExecutionFragment (ts: TransitionSystem) : Type _ := ts.ExecutionFragmentLike (ListProd ts.S ts.Act)
-/

end Nemonuri.TransitionSystem

end
