module

public import Nemonuri.SequenceProd.Sub

@[expose] public section

namespace Nemonuri.SequenceProd

inductive SubSpec (α β: Type _) where
  | refl (sp: SequenceProd α β)
  | «prefix» (pre: SequenceProd α β)
  | both (pre: SequenceProd α β) (suf: SequenceProd α β)

namespace SubSpec

variable {α β: Type _}

@[mk_iff]
inductive Mem (sp: SequenceProd α β) : SubSpec α β → Prop where
  | refl : Mem sp (.refl sp)
  | «prefix» (pre: SequenceProd α β) (req: IsPrefix pre sp) : Mem sp (.prefix pre)
  | both (pre: SequenceProd α β) (suf: SequenceProd α β) (req1: IsPrefix pre sp) (req2: IsSuffix suf sp) : Mem sp (.both pre suf)

def EvalToSet (spec: SubSpec α β) : Set (SequenceProd α β) := { sp | Mem sp spec }

end SubSpec


end Nemonuri.SequenceProd

end
