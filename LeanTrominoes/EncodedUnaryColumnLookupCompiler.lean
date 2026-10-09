/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.EncodedUnaryColumnCompiler

/-! # Total indexed unary lookup, including missing entries -/
noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Input Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol} {rows : Input → List Row} {query : Input → Row → Nat}
  {values : Input → List Nat}

def lookupValues (queries : Compiler encodeInput rows query)
    (table : TM2ComputableInPolyTime encodeInput unaryFields values) :
    Compiler encodeInput rows (fun s row => (values s).getD (query s row) 0) := by
  let bound := fun s => ((rows s).map (query s)).sum+1
  let padding : TM2ComputableInPolyTime encodeInput unaryFields (fun s => List.replicate (bound s) 0) := by
    let physical := constant (naturalRange (columnBound queries)) 0
    exact TM2ComputableInPolyTime.of_eq physical (fun s => by simp [bound])
  let padded := UnaryFieldClosure.appendCompiler encodeInput _ _ table padding
  let physical := UnaryIndexedValueLookup.valuesComputableInPolyTime encodeInput _ _ queries padded
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  congr 1
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro index member
    have small := List.le_sum_of_mem member
    simp only [List.length_append,List.length_replicate]
    dsimp only [bound]
    omega)]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro row _
  by_cases inside : query s row < (values s).length
  · exact List.getD_append _ _ _ _ inside
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_getD_replicate_default_eq]
    rw [List.getElem?_eq_none (by omega)]
    rfl

end LeanTrominoes.EncodedUnaryColumn
end
