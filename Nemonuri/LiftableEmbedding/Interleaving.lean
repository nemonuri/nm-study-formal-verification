module

public import Nemonuri.LiftableEmbedding.Basic
public import Nemonuri.LiftableEmbedding.Label

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.LiftableEmbedding


structure AreLiftable {L1 L2 R: Type*} (l1: LiftableEmbedding L1 R) (l2: LiftableEmbedding L2 R) (rv: R) : Prop where
  fst: l1.IsLiftable rv
  snd: l2.IsLiftable rv

inductive AnyLiftable {L1 L2 R: Type*} (l1: LiftableEmbedding L1 R) (l2: LiftableEmbedding L2 R) (rv: R) : Prop where
  | fst (req: l1.IsLiftable rv)
  | snd (req: l2.IsLiftable rv)

inductive IsExclusiveLiftable {L1 L2 R: Type*} (l1: LiftableEmbedding L1 R) (l2: LiftableEmbedding L2 R) (rv: R) : Label → Prop where
  | fst (req1: l1.IsLiftable rv) (req2: ¬l2.IsLiftable rv) : IsExclusiveLiftable l1 l2 rv .fst
  | snd (req1: ¬l1.IsLiftable rv) (req2: l2.IsLiftable rv) : IsExclusiveLiftable l1 l2 rv .snd

inductive AnyExclusiveLiftable {L1 L2 R: Type*} (l1: LiftableEmbedding L1 R) (l2: LiftableEmbedding L2 R) (rv: R) : Prop where
  | intro (lb: Label) (req: IsExclusiveLiftable l1 l2 rv lb)



end Nemonuri.LiftableEmbedding

end
