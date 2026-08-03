module

public import Nemonuri.Executions.ExecutionFragment.Raw

@[expose] public section

namespace Nemonuri.TransitionSystem.ExecutionFragment

inductive ExprRaw (ts: TransitionSystem) where
  | finite1 (total: ts.FiniteExecutionFragmentRaw)
  | finite2 (pre: ts.FiniteExecutionFragmentRaw) (post: ts.FiniteExecutionFragmentRaw)
  | infinite1 (pre: ts.FiniteExecutionFragmentRaw)

namespace ExprRaw

variable {ts: TransitionSystem}

def singleState (s: ts.S) : ExprRaw ts := .finite1 (.singleState s)

def ellipsis : ExprRaw ts := .infinite1 (⟨[],[]⟩)

def consEllipsis : ExprRaw ts → ExprRaw ts
  | .finite1 total => .finite2 (⟨[],[]⟩) total
  | x => x

def stepL (tail: ExprRaw ts) (s: ts.S) (a: ts.Act) : ExprRaw ts :=
  match tail with
  | .finite1 total => .finite1 (total.stepL s a)
  | .finite2 pre post => .finite2 (pre.stepL s a) post
  | .infinite1 pre => .infinite1 (pre.stepL s a)

instance : Coe ts.S (ExprRaw ts) := ⟨singleState⟩

end ExprRaw



end Nemonuri.TransitionSystem.ExecutionFragment

end
