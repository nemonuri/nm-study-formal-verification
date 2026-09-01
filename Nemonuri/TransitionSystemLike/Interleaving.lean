module

public import Nemonuri.TransitionSystemLike.Basic
public import Nemonuri.HasHUnion

/-!

## References

* [Christel Baier, Joost-Pieter Katoen, *Principles of Model Checking*][PoMC], p. 38

-/

@[expose] public section

namespace Nemonuri.TransitionSystem

universe us1 us2 uact_l uap_l uact_r uap_r

/-
class HasInterleaving (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) (Act: outParam <| Type uact_r) (AP: outParam <| Type uap_r) where
  act : HasHUnion.Bundle ts1.Act ts2.Act Act
  ap : HasHUnion.Bundle ts1.AP ts2.AP AP
-/

--attribute [reducible, instance] HasInterleaving.act HasInterleaving.ap


structure Interleaving (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l}) where
  act: HasHUnion.Bundle.{uact_l, uact_r} ts1.Act ts2.Act
  ap: HasHUnion.Bundle.{uap_l, uap_r} ts1.AP ts2.AP


--attribute [reducible, instance] Interleaving.actHasHUnionBundle Interleaving.apHasHUnionBundle

namespace Interleaving

open HasHUnion

variable {ts1: TransitionSystem.{us1, uact_l, uap_l}} {ts2: TransitionSystem.{us2, uact_l, uap_l}} --{Act: Type uact_r} {AP: Type uap_r}


--abbrev inferAt (Act AP: Type _) [i: HasInterleaving ts1 ts2 Act AP] : HasInterleaving ts1 ts2 Act AP := i

abbrev LeftActTypeAt (il: Interleaving ts1 ts2) (lb: Label) : Type _ := il.act.hasHUnion.LeftTypeAt ts1.Act ts2.Act lb

def embedActAt (il: Interleaving ts1 ts2) (lb: Label) (lv: il.LeftActTypeAt lb) : il.act.hasHUnion.R := il.act.hasHUnion.embedAt ts1.Act ts2.Act lb lv

--def embedActAt (Act AP: Type _) [HasInterleaving ts1 ts2 Act AP] (lb: Label) (lv: LeftActTypeAt Act AP lb) : Act := il.toActHasHUnion.embedAt ts1.Act ts2.Act lb lv



@[mk_iff]
inductive Transition (il: Interleaving ts1 ts2) : ts1.S → ts2.S → il.act.hasHUnion.R → ts1.S → ts2.S → Prop where
  | fst (s₁1: ts1.S) (a₁: ts1.Act) (s₁2: ts1.S) (req: s₁1 ─⌞a₁⌟→{ts1} s₁2) (s₂: ts2.S) : Transition il s₁1 s₂ (il.embedActAt .fst a₁) s₁2 s₂
  | snd (s₂1: ts2.S) (a₂: ts2.Act) (s₂2: ts2.S) (req: s₂1 ─⌞a₂⌟→{ts2} s₂2) (s₁: ts1.S) : Transition il s₁ s₂1 (il.embedActAt .snd a₂) s₁ s₂2

@[reducible]
def toTransitionSystem (il: Interleaving ts1 ts2) : TransitionSystem where
  S := ts1.S × ts2.S
  Act := letI := il.act.hasHUnion; HUnionElemAt ts1.Act ts2.Act
  I := Set.prod ts1.I ts2.I
  AP := letI := il.ap.hasHUnion; HUnionElemAt ts1.AP ts2.AP
  L s ap := letI := il.ap.memDecidable; il.ap.hasHUnion.hunionIndicator (ts1.labeling s.fst) (ts2.labeling s.snd) ap.val
  tr s1 a s2 := Transition il s1.fst s1.snd a s2.fst s2.snd

def toTransitionSystemActAP (il: Interleaving ts1 ts2) : TransitionSystem.OfActAP il.toTransitionSystem.Act il.toTransitionSystem.AP := il.toTransitionSystem.toActAP

def inferAt
  (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l})
  [HasHUnion.Bundle ts1.Act ts2.Act] [HasHUnion.Bundle ts1.AP ts2.AP]
  : Interleaving ts1 ts2 :=
  .mk inferInstance inferInstance

end Interleaving

def interleaveAt
  (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l})
  [HasHUnion.Bundle ts1.Act ts2.Act] [HasHUnion.Bundle ts1.AP ts2.AP]
  : TransitionSystem :=
  (Interleaving.inferAt ts1 ts2).toTransitionSystem


section InterleaveAt

open HasHUnion

--variable {ts1: TransitionSystem.{us1, uact_l, uap_l}} {ts2: TransitionSystem.{us2, uact_l, uap_l}} {Act: Type uact_l} {AP: Type uap_l}
--         [hbAct0: HasHUnion.Bundle ts1.Act ts2.Act Act] [hbAP0: HasHUnion.Bundle ts1.AP ts2.AP AP]
--         [hbAct: HasHUnion.Bundle ts1.Act Act Act] [hbAP: HasHUnion.Bundle ts1.AP AP AP]

/-
instance [HasHUnion.Bundle ts1.Act ts2.Act Act] [HasHUnion.Bundle ts1.AP ts2.AP AP] [HasHUnion.Bundle ts1.Act Act Act]
  : HasHUnion ts1.Act (interleaveAt Act AP ts1 ts2).Act Act where
  fst := hbAct.hasHUnion.fst
-/
/-

  snd :=
    let embed : (interleaveAt Act AP ts1 ts2).Act ↪ Act := .mk (Subtype.val) Subtype.val_injective
    {
      toEmbedding := embed
      lift rv req := Subtype.mk rv (by
          simp [hunionSetUnivAt_mem_iff] at req ⊢
          dsimp [embedAt, toLiftableEmbeddingAt]

        )
      lift_valid := _
    }
-/

/-
instance [HasHUnion.Bundle ts1.Act ts2.Act Act] [HasHUnion.Bundle ts1.AP ts2.AP AP] : HasHUnion.Bundle ts1.Act ((interleaveAt Act AP ts1 ts2).Act) Act where
  hasHUnion :=
-/

end InterleaveAt

/-
open Interleaving in
def interleave
  {ActL1 ActL2: Type uact_l} {APL1 APL2: Type uap_l} {ActR: Type uact_r} {APR: Type uap_r}
  (ts1: TransitionSystem.OfActAP ActL1 APL1) (ts2: TransitionSystem.OfActAP ActL2 APL2)
-/
/-
  (ts1: TransitionSystem.{us1, uact_l, uap_l}) (ts2: TransitionSystem.{us2, uact_l, uap_l})
  [HasHUnion.Bundle ts1.Act ts2.Act Act] [HasHUnion.Bundle ts1.AP ts2.AP AP]
  : TransitionSystem.OfActAP (inferAt ts1 ts2 Act AP).toTransitionSystem.Act (inferAt ts1 ts2 Act AP).toTransitionSystem.AP :=
  (inferAt ts1 ts2 Act AP).toTransitionSystem.toActAP
-/

/-
@[reducible]
def interleaving (ts1 ts2: TransitionSystem) : TransitionSystem where
  S := ts1.S × ts2.S
  Act := ts1.Act ⊕ ts2.Act
  I := Set.prod ts1.I ts2.I
  AP := ts1.AP ⊕ ts2.AP
-/


end Nemonuri.TransitionSystem

end
