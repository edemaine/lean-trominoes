/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathBatchSemantics

/-! # Kernel-checked search, backtracking, and reservation examples -/
namespace LeanTrominoes.BlockingPath.Examples

def branching : Buckets (Fin 4) (Fin 2) := fun v => match v.val with
  | 0 => [(0,some 1),(1,some 2)]
  | 1 => []
  | 2 => [(0,none)]
  | _ => [(0,none),(1,none)]

def result := batch branching 4 [0,3] initial
example : result.paths=[.cons 0 1 (.last 2 0),.last 3 1] := by decide +kernel
example : (List.finRange 4).map result.state.blocked=[true,true,true,true] := by decide +kernel
example : (List.finRange 4).map result.state.used=[true,false,true,true] := by decide +kernel
example : (List.finRange 2).map result.state.reserved=[true,true] := by decide +kernel
example : result.cost ≤ 20*((∑ v, (branching v).length)+4)+6*2+1 := by decide +kernel

-- A visited cycle fails without incorrectly reserving either vertex.
def cycle : Buckets (Fin 2) (Fin 1) := fun v => if v=0 then [(0,some 1)] else [(0,some 0)]
example : (batch cycle 2 [0] initial).paths=[] := by decide +kernel
example : (List.finRange 2).map (batch cycle 2 [0] initial).state.used=[false,false] := by decide +kernel

end LeanTrominoes.BlockingPath.Examples
