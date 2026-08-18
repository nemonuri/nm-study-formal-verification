module

public import Nemonuri.SequenceProdLike.Operations
public import Nemonuri.SequenceLike.AdHoc

@[expose] public section

namespace Nemonuri.SequenceProdLike

structure AdHoc (α β: Type _) where
  fst: SequenceLike.AdHoc α
  snd: SequenceLike.AdHoc β

namespace AdHoc

variable {α β: Type _}

/-
instance toSequenceProdLike : SequenceProdLike (AdHoc α β) α β where
  fst
-/

end AdHoc

end Nemonuri.SequenceProdLike

end
