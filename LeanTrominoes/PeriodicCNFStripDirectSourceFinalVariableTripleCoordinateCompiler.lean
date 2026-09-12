/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableOriginCompiler
import LeanTrominoes.PeriodicCNFStripGroupedVariableTriplePositionTable
import LeanTrominoes.SignedUnaryCoordinateIndexedTableExpansion

/-! # Native coordinate compiler for the actual variable-triple prefix -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private theorem pointValue_function (horizontal positive : Bool) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) =
      (fun point => SignedUnaryCoordinateRefinement.field positive
        (DelimitedDirectionDisplacement.component horizontal point)) := by
  funext point
  cases horizontal <;> cases positive <;> rfl

private theorem component_add (horizontal : Bool) (origin offset : Cell) :
    DelimitedDirectionDisplacement.component horizontal (Cell.add origin offset) =
      DelimitedDirectionDisplacement.component horizontal origin +
        DelimitedDirectionDisplacement.component horizontal offset := by
  cases horizontal <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance variableTripleCoordinatesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Expand each grouped variable origin using its finite fan-selected triple table. -/
def directSourceFinalVariableTripleCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateIndexedTableExpansion.values
    (fun pair => (groupedVariableTriplePositionTable pair).map
      (DelimitedDirectionDisplacement.component horizontal)) keepPositive
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (fun positive => directSourceFinalGroupedVariableOriginCoordinates decider horizontal positive symbols)

noncomputable def directSourceFinalVariableTripleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableTripleCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalVariableTripleCoordinates
  exact SignedUnaryCoordinateIndexedTableExpansion.nativeListComputableInPolyTime _ keepPositive
    (directSourceFinalGroupedVariableFanSlots decider)
    (fun positive => directSourceFinalGroupedVariableOriginCoordinates decider horizontal positive)
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
    (fun positive => directSourceFinalGroupedVariableOriginCoordinatesComputableInPolyTime decider horizontal positive)

/-- The complete variable prefix has exact coordinates and the canonical
variable, active-slot, and local-triple order. -/
theorem directSourceFinalVariableTripleCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalVariableTripleCoordinates decider horizontal keepPositive symbols =
      (horizontalThreeDMVariableTriplePositionsComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
          (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)) := by
  unfold directSourceFinalVariableTripleCoordinates
  simp only [directSourceFinalGroupedVariableFanSlots_eq_horizontal,
    directSourceFinalGroupedVariableOriginCoordinates_eq_horizontal, pointValue_function]
  rw [SignedUnaryCoordinateIndexedTableExpansion.values_map _ _ _ _ _ (fun entry _ => by
    rw [List.length_map]
    exact groupedVariableTriplePositionTable_length_pos _),
    ← groupedVariableTriplePositionTables_eq_horizontal]
  simp only [List.map_flatMap, List.map_map, Function.comp_def, component_add]

/-- The actual geometric prefix has an unconditional polynomial-time compiler. -/
noncomputable def directSourceFinalHorizontalVariableTripleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalThreeDMVariableTriplePositionsComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
          (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalVariableTripleCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableTripleCoordinates_eq_horizontal decider horizontal keepPositive symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
