module

public import Nemonuri.TransitionSystemLike.ProgramGraph.Interleaving.Basic
public import Nemonuri.Relations.Heterogeneous.SumRelGen.CanShare


/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 40

-/


@[expose] public section

set_option autoImplicit false

namespace Nemonuri.ProgramGraph.Interleaving.EvalEquiv.ProgramGraphUnion

variable {CCL CCR ECL VarL ValL ValSL ECR VarR ValR ValSR: Type*}
         [SetLike ValSL ValL] [SetLike ValSR ValR] [EvalLike ECL VarL ValL] [EvalLike ECR VarR ValR]
         [StandardType.ConcreteFinite ECL VarL ValL ValSL] [StandardType.ConcreteFinite ECR VarR ValR ValSR]
         [FiniteCondLike CCL ECL VarL ValL ValSL] [FiniteCondLike CCR ECR VarR ValR ValSR]
         {il: EvalEquiv ECL VarL ValL ECR VarR ValR}

open Nemonuri.Relations.Heterogeneous

/-!

The distinction between local and shared variables has also an impact on the actions of the composed program graph.

Actions that access (i.e., inspect or modify) shared variables may be considered as "critical"; otherwise, they are viewed to be noncritical.

-/


structure IsNonCritical (pgu: il.ProgramGraphUnion ValSL ValSR CCL CCR) (act: pgu.Act) : Prop where
  /-- `act` does not inspect shared variables. -/
  depends_on_local (ec1 ec2: il.EvalInter ECL ECR) (req: ∀(var: SumUnion il.var.Rel), (¬var.CanShare) → ec1 var = ec2 var) : pgu.effect act ec1 = pgu.effect act ec2
  /-- `act` does not modify shared variables. -/
  preserves_shared (ec: il.EvalInter ECL ECR) (var: SumUnion il.var.Rel) (req: var.CanShare) : ec var = pgu.effect act ec var

def IsCritical (pgu: il.ProgramGraphUnion ValSL ValSR CCL CCR) (act: pgu.Act) : Prop := ¬(IsNonCritical pgu act)

/-!

The difference between the critical and noncritical actions becomes clear when interpreting the (possible) nondeterminism in the transition system.

Nondeterminism in a state of this transition system may stand either for

-/

end Nemonuri.ProgramGraph.Interleaving.EvalEquiv.ProgramGraphUnion
