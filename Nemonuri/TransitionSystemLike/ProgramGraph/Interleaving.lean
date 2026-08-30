module

public import Nemonuri.TransitionSystemLike.ProgramGraph.Basic
public import Nemonuri.HasHUnion

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 40

-/

@[expose] public section

namespace Nemonuri.ProgramGraph

open HasHUnion

namespace Eval

universe uvar_l uval_l uvar_r uval_r

structure Interleaving
  {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l}
  (ec1 : Eval VarL1 ValL1) (ec2: Eval VarL2 ValL2) (VarR: Type uvar_r) (ValR: Type uval_r) where
  var: Bundle VarL1 VarL2 VarR
  val: Bundle ValL1 ValL2 ValR
  sel: letI := var.hasHUnion; HInterElemAt VarL1 VarL2 VarR → Label

namespace Interleaving

variable {VarL1 VarL2: Type uvar_l} {ValL1 ValL2: Type uval_l}
         {ec1 : Eval VarL1 ValL1} {ec2: Eval VarL2 ValL2} {VarR: Type uvar_r} {ValR: Type uval_r}

set_option trace.Meta.synthInstance true in
def eval (il: Interleaving ec1 ec2 VarR ValR) : (letI := il.var; HUnionElemAt VarL1 VarL2 VarR) → ValR :=
  letI := il.var.hasHUnion; letI := il.var.memDecidable
  letI := il.val.hasHUnion; letI := il.val.memDecidable
  hunionMapAt VarL1 VarL2 VarR ValL1 ValL2 ValR (ec1: VarL1 → ValL1) (ec2: VarL2 → ValL2) il.sel





end Interleaving



end Eval


--structure Interleaving

--namespace Interleaving

--end Interleaving

end Nemonuri.ProgramGraph

end
