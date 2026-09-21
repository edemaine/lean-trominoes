/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingFlatEncoding
import LeanTrominoes.PeriodicPlanarSATOneDimensional
import LeanTrominoes.PartrecDynamicDropSpace

/-! # Native flat encoding of a periodic formula with its drawing

A length-delimited drawing precedes the formula. Both components use their
existing flat binary formats; the drawing contains the complete route lists.
The formula projection is a space-certified dynamic suffix selection.
-/
namespace LeanTrominoes.PeriodicPlanarSAT.FlatEncoding
open PeriodicCNFFlatEncoding
open Turing Turing.ToPartrec Turing.PartrecToTM2

abbrev drawingFields := PeriodicGridDrawing.Arithmetic.fields

def fields (input : Input Nat) : List Nat :=
  (drawingFields input.2).length :: (drawingFields input.2 ++ formulaFields input.1)

def decodeFields : List Nat → Option (Input Nat)
  | size :: rest => do
    let drawing ← PeriodicGridDrawing.Arithmetic.decodeFields (rest.take size)
    let formula ← decodeFormulaFields (rest.drop size)
    return (formula,drawing)
  | [] => none

theorem decodeFields_fields (input : Input Nat) : decodeFields (fields input) = some input := by
  simp [fields,decodeFields,
    PeriodicGridDrawing.Arithmetic.decodeFields_fields,decodeFormulaFields_formulaFields]

def finEncoding : _root_.Computability.FinEncoding (Input Nat) :=
  finEncodingOfFields fields decodeFields decodeFields_fields

theorem fields_space (input : Input Nat) :
    encodedListSpace (fields input) = (finEncoding.encode input).length := by
  change encodedListSpace (fields input) = (encodeNatFields (fields input)).length
  rw [encodeNatFields_length,encodedListSpace_eq_sum]

theorem formulaProjection_eval (input : Input Nat) :
    Code.dynamicDropCode.eval (fields input) = pure (formulaFields input.1) := by
  simp [fields,Code.dynamicDropCode_eval]

theorem formulaProjection_fits (input : Input Nat) :
    EvaluatorCodeFits Code.dynamicDropCode (fields input) (formulaFields input.1)
      (1000000*((finEncoding.encode input).length+1)) := by
  have h := EvaluatorCodeFits.dynamicDrop (drawingFields input.2).length
    (drawingFields input.2 ++ formulaFields input.1)
  rw [← fields_space]
  simpa only [List.drop_left,EvaluatorCodeFits.dynamicDropCost,fields] using h

theorem formula_space_le (input : Input Nat) :
    (PeriodicCNFFlatEncoding.finEncoding.encode input.1).length ≤ (finEncoding.encode input).length := by
  have h := EvaluatorCodeFits.dynamicDropSpace_drop_le (drawingFields input.2).length
    (drawingFields input.2 ++ formulaFields input.1)
  rw [List.drop_left] at h
  rw [← fields_space]
  simp only [fields,encodedListSpace_cons]
  rw [PeriodicCNFFlatEncoding.finEncoding_encode_length,← encodedListSpace_eq_sum]
  omega

end LeanTrominoes.PeriodicPlanarSAT.FlatEncoding
