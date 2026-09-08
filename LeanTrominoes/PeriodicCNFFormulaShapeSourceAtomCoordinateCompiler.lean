/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeData
import LeanTrominoes.UnaryFieldRangeCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler

/-! # Source-atom coordinate fields from finite formula shapes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.FormulaShapeSourceAtomCoordinates

open Computability Turing FormulaShape

private def zeroBlock : Token → List UnaryFieldEncoderMachine.Symbol
  | .variable => [.delimiter]
  | .clause _ => []

private def zeroFields (shape : List Token) : List Nat :=
  List.replicate (variableCount shape) 0

private theorem zeroBlock_eq (shape : List Token) :
    shape.flatMap zeroBlock = UnaryFieldEncoderMachine.unaryFields (zeroFields shape) := by
  induction shape with
  | nil => rfl
  | cons token shape induction =>
      cases token <;>
        simp [zeroBlock, zeroFields, variableCount, variableMarkers,
          List.replicate_succ, UnaryFieldEncoderMachine.unaryFields,
          UnaryFieldEncoderMachine.unaryField] at induction ⊢ <;> exact induction

private noncomputable def zeroFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields zeroFields :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (FiniteBlockTransducer.computableInPolyTime zeroBlock) zeroBlock_eq

/-- Canonical deduplicated variable indices are consecutive by construction. -/
def indices (shape : List Token) : List Nat := List.range (variableCount shape)

noncomputable def indicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields indices := by
  let compiled := TM2CompositionMachine.computableInPolyTime
    zeroFieldsComputableInPolyTime UnaryFieldRange.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun shape => by simp [UnaryFieldRange.values, zeroFields, indices])

def factor (horizontal keepPositive : Bool) : Nat :=
  if horizontal && keepPositive then 160 else 0

def offset (horizontal keepPositive : Bool) : Nat :=
  if keepPositive then (if horizontal then 86 else 47) else 0

/-- The four signed fields of the source atom with index i. -/
def coordinate (horizontal keepPositive : Bool) (index : Nat) : Nat :=
  index * factor horizontal keepPositive + offset horizontal keepPositive

def values (horizontal keepPositive : Bool) (shape : List Token) : List Nat :=
  UnaryFieldConstantOffsets.values (offset horizontal keepPositive)
    (UnaryFieldConstantScale.values (factor horizontal keepPositive) (indices shape))

theorem values_eq_map (horizontal keepPositive : Bool) (shape : List Token) :
    values horizontal keepPositive shape =
      (List.range (variableCount shape)).map (coordinate horizontal keepPositive) := by
  simp [values, indices, UnaryFieldConstantScale.values,
    UnaryFieldConstantOffsets.values, List.map_map, Function.comp_def, coordinate]

/-- Range generation followed by fixed unary scaling and offset produces
all source-variable coordinate fields in polynomial time. -/
noncomputable def valuesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (values horizontal keepPositive) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun shape => UnaryFieldConstantOffsets.values (offset horizontal keepPositive)
      (UnaryFieldConstantScale.values (factor horizontal keepPositive) (indices shape)))
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime indicesComputableInPolyTime
      (UnaryFieldConstantScale.computableInPolyTime (factor horizontal keepPositive)))
    (UnaryFieldConstantOffsets.computableInPolyTime (offset horizontal keepPositive))

end LeanTrominoes.PeriodicCNF.FormulaShapeSourceAtomCoordinates

end
