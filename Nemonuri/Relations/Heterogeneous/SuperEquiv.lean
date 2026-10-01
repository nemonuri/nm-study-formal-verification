module

public import Nemonuri.Relations.Heterogeneous.IsSub

@[expose] public section

set_option autoImplicit false

namespace Nemonuri.Relations.Heterogeneous

universe uh

structure SuperEquivStruct (α β: Sort*) where
  toFun: α → β
  invFun: β → α

structure IsSuperEquiv {α β: Sort*} (rel: α → β → Prop) (s: SuperEquivStruct α β) : Prop where
  isSubOfEquiv : IsSubOfEquiv rel s.toFun s.invFun

structure SuperEquiv {α β: Sort*} (rel: α → β → Prop) extends toStruct: SuperEquivStruct α β where
  valid: IsSuperEquiv rel toStruct

end Nemonuri.Relations.Heterogeneous

end
