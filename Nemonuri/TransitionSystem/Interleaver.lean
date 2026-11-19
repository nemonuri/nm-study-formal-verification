module

public import Nemonuri.TransitionSystem.Executor
public import Nemonuri.TypeLists.BiIter.SumEquiv
public import Nemonuri.TransitionSystem.Properties
--public import Nemonuri.Relations.Heterogeneous.SumRelGen

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 38

-/

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.TransitionSystem

open Nemonuri.Relations.Heterogeneous

open TypeLists.BiIter IterRel₂

universe u1 u2 u3


def Interleaver.IterIsActApEq (trs: List (TransitionSystem.{u1, u2, u3})) (actTys: List (Type u2)) (apTys: List (Type u3)) : Type _ := IterActAPType (fun tr Act AP _ _ _ => IsActApEq tr Act AP) trs actTys apTys

structure Interleaver (tr: TransitionSystem.{u1, u2, u3}) (Act: Type u2) (AP: Type u3) (trs: List (TransitionSystem.{u1, u2, u3})) (actTys: List (Type u2)) (apTys: List (Type u3)) where
  actIterRel₂: IterRel₂ (Act::actTys)
  apIterRel₂: IterRel₂ (AP::apTys)
  iterIsActApEq: Interleaver.IterIsActApEq (tr::trs) (Act::actTys) (AP::apTys)


namespace Interleaver

variable {tr2: TransitionSystem.{u1, u2, u3}} {Act2: Type u2} {AP2: Type u3} {trs: List (TransitionSystem.{u1, u2, u3})} {actTys: List (Type u2)} {apTys: List (Type u3)}

def single (tr: TransitionSystem.{u1, u2, u3}) (Act: Type u2) (AP: Type u3) (req: IsActApEq tr Act AP) : Interleaver tr Act AP [] [] [] where
  actIterRel₂ := .single Act
  apIterRel₂ := .single AP
  iterIsActApEq := .cons tr Act AP [] [] [] (req) .nil

def cons (tr: TransitionSystem.{u1, u2, u3}) (Act: Type u2) (AP: Type u3) (req: IsActApEq tr Act AP)
         (actIterRel: IterRel (Act::Act2::actTys)) (apIterRel: IterRel (AP::AP2::apTys))
         (il: Interleaver tr2 Act2 AP2 trs actTys apTys) : Interleaver tr Act AP (tr2::trs) (Act2::actTys) (AP2::apTys) where
  actIterRel₂ := .cons Act Act2 actTys actIterRel il.actIterRel₂
  apIterRel₂ := .cons AP AP2 apTys apIterRel il.apIterRel₂
  iterIsActApEq := .cons tr Act AP _ _ _ req il.iterIsActApEq



end Interleaver


/-
variable (trs: List (TransitionSystem.{u1, u2, u3})) (actTys: List (Type u2)) (apTys: List (Type u3))
         (irelAct: IterRel₂ actTys) (irelAp: IterRel₂ apTys) (ireq: IterActAPType (fun tr Act AP _ _ _ => IsActApEq tr Act AP) trs actTys apTys)
-/



/-
structure InterleaverStruct (ts1 ts2: TransitionSystem) where
  areActHEq: ts1.Act → ts2.Act → Bool
  areApHEq: ts1.AP → ts2.AP → Bool

structure IsInterleaver {ts1 ts2: TransitionSystem} (s: InterleaverStruct ts1 ts2) : Prop where
  areActHEq_biUnique: Relator.BiUnique (s.areActHEq · · = .true)
  areApHEq_biUnique: Relator.BiUnique (s.areApHEq · · = .true)
-/

end Nemonuri.TransitionSystem

end
