/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableTripleCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseTripleCoordinateCompiler
import LeanTrominoes.UnaryFieldEncoderAppendClosure
import LeanTrominoes.UnaryFieldFixedCopiesCompiler

/-! # Complete canonical triple coordinates from the direct source -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Concatenate the variable prefix and clause suffix in actual triple order. -/
def directSourceFinalTripleCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalVariableTripleCoordinates decider horizontal keepPositive symbols ++
    directSourceFinalClauseTripleCoordinates decider horizontal keepPositive symbols

noncomputable def directSourceFinalTripleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTripleCoordinates decider horizontal keepPositive) := by
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalVariableTripleCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (directSourceFinalClauseTripleCoordinatesComputableInPolyTime decider horizontal keepPositive)

theorem directSourceFinalTripleCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalTripleCoordinates decider horizontal keepPositive symbols =
      (horizontalThreeDMTriplePositionsComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
        (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)) := by
  rw [directSourceFinalTripleCoordinates, directSourceFinalVariableTripleCoordinates_eq_horizontal,
    directSourceFinalClauseTripleCoordinates_eq_horizontal,
    horizontalThreeDMTriplePositionsComputed_eq_blocks, List.map_append]

noncomputable def directSourceFinalHorizontalTripleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalThreeDMTriplePositionsComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
          (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalTripleCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTripleCoordinates_eq_horizontal decider horizontal keepPositive symbols))

@[simp] theorem directSourceFinalTripleCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalTripleCoordinates decider horizontal keepPositive symbols).length =
      (horizontalThreeDMTriplePositionsComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).length := by
  rw [directSourceFinalTripleCoordinates_eq_horizontal, List.length_map]

/-- Each triple contributes the same source position to its red, green and
blue incidences, in canonical triple-major order. -/
def directSourceFinalIncidenceSourceCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldFixedCopies.values 3 (directSourceFinalTripleCoordinates decider horizontal keepPositive symbols)

noncomputable def directSourceFinalIncidenceSourceCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalIncidenceSourceCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalIncidenceSourceCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalTripleCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (UnaryFieldFixedCopies.computableInPolyTime 3)

theorem directSourceFinalIncidenceSourceCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalIncidenceSourceCoordinates decider horizontal keepPositive symbols =
      (horizontalThreeDMTriplePositionsComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).flatMap
        (fun point => List.replicate 3
          (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) point)) := by
  rw [directSourceFinalIncidenceSourceCoordinates, directSourceFinalTripleCoordinates_eq_horizontal]
  simp only [UnaryFieldFixedCopies.values, List.flatMap_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
