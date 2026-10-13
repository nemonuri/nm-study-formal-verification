module

public import Nemonuri.Relations.Heterogeneous.Label
public import Nemonuri.Relations.Heterogeneous.MemAt

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe u1 u2

variable {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2}

inductive SeqRel (piRel: ((x: α1) → (β1 x)) → ((x: α2) → (β2 x)) → Prop) (domRel: α1 → α2 → Prop) (x1: α1) (x2: α2) : (β1 x1) → (β2 x2) → Prop where
  | intro (pi1: (x: α1) → (β1 x)) (pi2: (x: α2) → (β2 x)) (req1: piRel pi1 pi2) (req2: domRel x1 x2) :
          SeqRel piRel domRel x1 x2 (pi1 x1) (pi2 x2)

inductive SigmaPredOfPiPred {α: Sort u1} {β: α → Sort u2} (piPred: ((x: α) → (β x)) → Prop) : (x: α) → (β x) → Prop where
  | intro (pi: (x: α) → (β x)) (req: piPred pi) (x: α) : SigmaPredOfPiPred piPred x (pi x)

section

/-
variable {α: Sort u1} {β: α → Sort u2}

inductive ArePartialSigmaStampRel (cond: ((x: α) → (β x)) → Prop) (x: α) (y: β x) (pi: (x: α) → (β x)) : Prop where
  | pos (req1: cond pi) (req2: pi x = y)
  | neg (req: ∀(pi0: (x: α) → (β x)), (pi0 x = y) → ¬cond pi0)
-/

structure SigmaStampStruct (α: Sort u1) (β: α → Sort u2) where
  stamp (x1: α) (y1: β x1) (x2: α) : β x2

/-
def IsPartialSigmaStamp (cond: ((x: α) → (β x)) → Prop) (s: SigmaStampStruct α β) : Prop :=
  ∀⦃x: α⦄ ⦃pi: (x: α) → (β x)⦄, ArePartialSigmaStampRel cond x (pi x) (s.stamp x (pi x))


@[defeq]
theorem isPartialSigmaStamp_def {cond: ((x: α) → (β x)) → Prop} {s: SigmaStampStruct α β}
  : IsPartialSigmaStamp cond s = ((x: α) → (pi: (x: α) → (β x)) → ArePartialSigmaStampRel cond x (pi x) (s.stamp x (pi x))) :=
  rfl
-/

/-
structure PartialSigmaStamp (α: Sort u1) (β: α → Sort u2) (cond: ((x: α) → (β x)) → Prop) where
  stamp: (x0: α) → (β x0) → (x: α) → (β x)
  valid: IsPartialSigmaStamp cond stamp
-/

end

--{α1 α2: Sort u1} (β1: α1 → Sort u2) (β2: α2 → Sort u2) --(lb: Label) → (lb.MatchSort α1 α2 → Sort u2)

structure SigmaStampProdStruct (α1 α2: Sort u1) (β1: α1 → Sort u2) (β2: α2 → Sort u2) where
  fst: SigmaStampStruct α1 β1
  snd: SigmaStampStruct α2 β2

structure IsPartialSigmaStampProd {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2}
  (s: SigmaStampProdStruct α1 α2 β1 β2) (condX: α1 → α2 → Prop) (condPi: ((x0: α1) → (β1 x0)) → ((x0: α2) → (β2 x0)) → Prop)
  (x1: α1) (x2: α2) (pi1: (x0: α1) → (β1 x0)) (pi2: (x0: α2) → (β2 x0)) (req1: condX x1 x2) (req2: condPi pi1 pi2) : Prop where
  stamp_rel: condPi (s.fst.stamp x1 (pi1 x1)) (s.snd.stamp x2 (pi2 x2))
  fst_stamp_eq: s.fst.stamp x1 (pi1 x1) x1 = pi1 x1
  snd_stamp_eq: s.snd.stamp x2 (pi2 x2) x2 = pi2 x2
/-
  | pos (req1: condX x1 x2)
        (req2: ∀(pi1: (x0: α1) → (β1 x0)) (pi2: (x0: α2) → (β2 x0)), condPi pi1 pi2 →
                (condPi (s.fst.stamp x1 (pi1 x1)) (s.snd.stamp x2 (pi2 x2))) ∧ (s.fst.stamp x1 (pi1 x1) x1 = pi1 x1) ∧ (s.snd.stamp x2 (pi2 x2) x2 = pi2 x2))
  | neg (req: ¬condX x1 x2)
-/

structure PartialSigmaStampProd {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2} (condX: α1 → α2 → Prop) (condPi: ((x0: α1) → (β1 x0)) → ((x0: α2) → (β2 x0)) → Prop)
  extends toStruct: SigmaStampProdStruct α1 α2 β1 β2 where
  valid x1 x2 pi1 pi2 req1 req2 : IsPartialSigmaStampProd toStruct condX condPi x1 x2 pi1 pi2 req1 req2


/-
structure IsSigmaStampProd {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2} (cond: ((x0: α1) → (β1 x0)) → ((x0: α2) → (β2 x0)) → Prop) (s: SigmaStampProdStruct α1 α2 β1 β2) : Prop where
  fst: IsPartialSigmaStamp (MemAt cond .fst) s.fst
  snd: IsPartialSigmaStamp (MemAt cond .snd) s.snd


-/

/-
inductive SigmaStampSumStruct (α1 α2: Sort u1) (β1: α1 → Sort u2) (β2: α2 → Sort u2) where
  | fst (stamp: (x: α1) → (β1 x) → (x2: α1) → (β1 x2))
  | snd (stamp: (x: α2) → (β2 x) → (x2: α2) → (β2 x2))
  --| fst (β: α1 → Sort u2) (stamp: (x: α1) → (β x) → (x2: α1) → (β x2)) : SigmaStampSumStruct α1 α2 (.inl β)
  --| snd (β: α2 → Sort u2) (stamp: (x: α2) → (β x) → (x2: α2) → (β x2)) : SigmaStampSumStruct α1 α2 (.inr β)

inductive IsSigmaStampSum {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2} (cond: ((x0: α1) → (β1 x0)) → ((x0: α2) → (β2 x0)) → Prop) : (SigmaStampSumStruct α1 α2 β1 β2) → Prop where
  | fst (stamp: (x: α1) → (β1 x) → (x2: α1) → (β1 x2)) (req: IsPartialSigmaStamp (MemAt cond .fst) stamp) : IsSigmaStampSum cond (.fst stamp)
  | snd (stamp: (x: α2) → (β2 x) → (x2: α2) → (β2 x2)) (req: IsPartialSigmaStamp (MemAt cond .snd) stamp) : IsSigmaStampSum cond (.snd stamp)

structure SigmaStampSum {α1 α2: Sort u1} {β1: α1 → Sort u2} {β2: α2 → Sort u2} (cond: ((x0: α1) → (β1 x0)) → ((x0: α2) → (β2 x0)) → Prop) where
  toStruct: SigmaStampSumStruct α1 α2 β1 β2
  valid: IsSigmaStampSum cond toStruct
-/

/-
inductive IsSigmaStampSum (α1 α2: Sort u1) (cond: (lb: Label) → lb.MatchSort α1 α2 → Prop) : (lb: Label) → (β: lb.MatchSort α1 α2 → Sort u2) → (SigmaStampSumStruct α1 α2 lb β) → Prop where
  | fst (β: α1 → Sort u2) (stamp: (x: α1) → (β x) → (x2: α1) → (β x2)) (req: IsPartialSigmaStamp (cond .fst) stamp) : IsSigmaStampSum
-/

  --fst: (x0: α1) → (β1 x0) → (x: α1) → (β1 x)
  --snd: (x0: α2) → (β2 x0) → (x: α2) → (β2 x)

/-
structure IsSigmaStampProd (s: SigmaStampProdStruct β1 β2) (cond: ((x0: α1) → (β1 x0)) → ((x0: α2) → (β2 x0)) → Prop) : Prop where
  fst: IsPartialSigmaStamp (MemAt cond .fst) s.fst
  snd: IsPartialSigmaStamp (MemAt cond .snd) s.snd
-/
  --fst: IsPartialSigmaStamp cond

--structure SigmaStampProd


def seqAreRel (stamp1: (x0: α1) → (β1 x0) → (x: α1) → (β1 x)) (stamp2: (x0: α2) → (β2 x0) → (x: α2) → (β2 x))
              (piAreRel: ((x: α1) → (β1 x)) → ((x: α2) → (β2 x)) → Bool) (domAreRel: α1 → α2 → Bool)
              (x1: α1) (x2: α2) (y1: β1 x1) (y2: β2 x2) : Bool :=
  domAreRel x1 x2 && piAreRel (stamp1 x1 y1) (stamp2 x2 y2)



end Nemonuri.Relations.Heterogeneous

end
