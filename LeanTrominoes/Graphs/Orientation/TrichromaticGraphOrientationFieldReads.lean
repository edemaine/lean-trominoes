/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFieldQueries

/-! # Ordinary list lookup in the native graph field tables -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding
open Gadget BoundedArithmetic BoundedArithmetic.Expr

theorem recordField_getD (graph : Input) (index : Nat) (field : Fin 5) (bound : index < graph.2.length) :
    (fields graph).getD (2+graph.1.length+5*index+field.val) 0 =
      (edgeFields graph.2[index]).getD field.val 0 := by
  have read := FieldQueries.entry_eval graph [] (.literal index) field (by simpa [Expr.eval] using bound)
  have header : (fields graph)[0]?.getD 0 = graph.1.length := rfl
  simp only [FieldQueries.entry,Expr.eval,Op.eval,eval_var,List.length_nil,List.nil_append,
    Nat.zero_add,header] at read
  simpa only [List.getD_eq_getElem?_getD] using read

theorem vertexKind_getD (graph : Input) (vertex : Nat) (bound : vertex < graph.1.length) :
    (fields graph).getD (2+vertex) 0 = (graph.1.getD vertex false).toNat := by
  simp only [fields,List.getD_eq_getElem?_getD]
  have address : 2+vertex = vertex+1+1 := by omega
  rw [address]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using bound)]
  simp [List.getElem?_map,List.getElem?_eq_getElem bound]

end LeanTrominoes.TrichromaticGraphOrientation.FlatEncoding
