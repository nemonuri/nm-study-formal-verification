module

public meta import Nemonuri.Executions.Specs.Tactic
public import Nemonuri.Executions.Basic
public import Nemonuri.SequenceProd.Specs.SubSpec

@[expose] public section

namespace Nemonuri.TransitionSystem

open Sequence
open SequenceProd

def ExecutionFragmentSpec (ts: TransitionSystem) : Type _ := SubSpec ts.S ts.Act

namespace ExecutionFragmentSpec

variable {ts: TransitionSystem} {sp sp2: SequenceProd ts.S ts.Act}

@[defeq, exec_spec_norm ←]
theorem eq_subspec : ts.ExecutionFragmentSpec = SubSpec ts.S ts.Act := rfl

@[match_pattern]
def refl (sp: SequenceProd ts.S ts.Act) : ts.ExecutionFragmentSpec := SubSpec.refl sp

@[defeq, exec_spec_norm ←]
theorem refl_def : refl sp = SubSpec.refl sp := rfl

@[match_pattern]
def «prefix» (sp: SequenceProd ts.S ts.Act) : ts.ExecutionFragmentSpec := SubSpec.prefix sp

@[defeq, exec_spec_norm ←]
theorem prefix_def : «prefix» sp = SubSpec.prefix sp := rfl

@[match_pattern]
def both (pre suf: SequenceProd ts.S ts.Act) : ts.ExecutionFragmentSpec := SubSpec.both pre suf

@[defeq, exec_spec_norm ←]
theorem both_def : both sp sp2 = SubSpec.both sp sp2 := rfl

section Operations

variable {s: ts.S} {act: ts.Act}

def single (s: ts.S) : ts.ExecutionFragmentSpec := .refl (.singleFst ts.S ts.Act s)

@[defeq, exec_spec_norm]
theorem single_def : single s = .refl (.singleFst ts.S ts.Act s) := rfl

def ellipsis : ts.ExecutionFragmentSpec := .both .nil .nil

@[defeq, exec_spec_norm]
theorem ellipsis_def : @ellipsis ts = .both .nil .nil := rfl


def consEllipsis : ts.ExecutionFragmentSpec → ts.ExecutionFragmentSpec
  | .refl sp => .both .nil sp
  | x => x

@[defeq, exec_spec_norm]
theorem consEllipsis_refl : consEllipsis (.refl sp) = .both .nil sp := rfl


def stepL (s: ts.S) (act: ts.Act) : ts.ExecutionFragmentSpec → ts.ExecutionFragmentSpec
  | .refl sp => .refl (.stepL s act sp)
  | .prefix pre => .prefix (.stepL s act pre)
  | .both pre suf => .both (.stepL s act pre) suf


@[defeq, exec_spec_norm]
theorem stepL_refl : stepL s act (.refl sp) = .refl (.stepL s act sp) := rfl

@[defeq, exec_spec_norm]
theorem stepL_prefix : stepL s act (.prefix sp) = .prefix (.stepL s act sp) := rfl

@[defeq, exec_spec_norm]
theorem stepL_both : stepL s act (.both sp sp2) = .both (.stepL s act sp) sp2 := rfl

attribute [exec_spec_norm]
  SequenceProd.stepL_getAt?_zero SequenceProd.stepL_getAt?_add_one_at
  SequenceProd.singleFst_getAt?_zero SequenceProd.singleFst_getAt?_add_one
  SequenceProd.nil_getAt?

instance : Coe ts.S ts.ExecutionFragmentSpec := ⟨single⟩

end Operations

structure Mem (sp: SequenceProd ts.S ts.Act) (ef: ts.ExecutionFragmentSpec) : Prop where
  subSpec_mem: SubSpec.Mem sp (eq_subspec ▸ ef)
  executionFragment : IsExecutionFragment sp

def EvalToSet (ef: ts.ExecutionFragmentSpec) : Set (SequenceProd ts.S ts.Act) := { sp | Mem sp ef }

end ExecutionFragmentSpec

end Nemonuri.TransitionSystem

end
