/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityVariableCoordinateHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPolarityClauseCoordinateHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalGadgetOriginAffineCoordinates

/-! # Native coordinate columns for actual horizontal gadget origins -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Fixed offsets inside the macrocell for variable and clause gadgets. -/
def horizontalGadgetOriginOffset (isVariable : Bool) : Cell :=
  if isVariable then (20, 64) else (50, 60)

private theorem pointValue_bools (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.component horizontal point) := by
  cases horizontal <;> cases positive <;> rfl

private theorem pointValue_function (horizontal positive : Bool) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) =
      (fun point => SignedUnaryCoordinateRefinement.field positive
        (DelimitedDirectionDisplacement.component horizontal point)) := by
  funext point
  exact pointValue_bools horizontal positive point

private theorem component_affine (horizontal : Bool) (origin offset : Cell) :
    DelimitedDirectionDisplacement.component horizontal (Cell.add (Cell.scale 256 origin) offset) =
      (256 : Int) * DelimitedDirectionDisplacement.component horizontal origin +
        DelimitedDirectionDisplacement.component horizontal offset := by
  cases horizontal <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance gadgetOriginCoordinatesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Routed endpoints before padding and macrocell placement, in occurrence order. -/
def directSourceFinalRoutedVertexPoints (isVariable : Bool) (symbols : List encoding.Γ) : List Cell :=
  if isVariable then
    (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
      (horizontalRoutedPlacementComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).position
  else
    presentedIncidenceClausePositions
      (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))
      (horizontalRoutedPlacementComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))

def directSourceFinalRoutedVertexCoordinates (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  if isVariable then directSourceFinalPolarityVariableCoordinates decider horizontal keepPositive symbols
  else directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive symbols

noncomputable def directSourceFinalRoutedVertexCoordinatesComputableInPolyTime (isVariable horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRoutedVertexCoordinates decider isVariable horizontal keepPositive) := by
  cases isVariable
  · exact directSourceFinalPolarityClauseCoordinatesComputableInPolyTime decider horizontal keepPositive
  · exact directSourceFinalPolarityVariableCoordinatesComputableInPolyTime decider horizontal keepPositive

@[simp] theorem directSourceFinalRoutedVertexCoordinates_length (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalRoutedVertexCoordinates decider isVariable horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  cases isVariable <;> simp [directSourceFinalRoutedVertexCoordinates]

theorem directSourceFinalRoutedVertexCoordinates_eq_points (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalRoutedVertexCoordinates decider isVariable horizontal keepPositive symbols =
      (directSourceFinalRoutedVertexPoints decider isVariable symbols).map
        (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)) := by
  cases isVariable <;> simp only [directSourceFinalRoutedVertexCoordinates, directSourceFinalRoutedVertexPoints, Bool.false_eq_true, ↓reduceIte]
  · simpa only [directSourceFinalHorizontalClauseCoordinates] using
      directSourceFinalPolarityClauseCoordinates_eq_horizontal decider horizontal keepPositive symbols
  · simpa only [List.map_map, Function.comp_def] using
      directSourceFinalPolarityVariableCoordinates_eq_horizontal decider horizontal keepPositive symbols

@[simp] theorem directSourceFinalRoutedVertexPoints_length (isVariable : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalRoutedVertexPoints decider isVariable symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  have lengths := congrArg List.length (directSourceFinalRoutedVertexCoordinates_eq_points decider isVariable true true symbols)
  simpa only [directSourceFinalRoutedVertexCoordinates_length, List.length_map] using lengths.symm

private theorem constantHeaderCoordinates_eq_points (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalHeaderPointCoordinates decider (fun _ => horizontalGadgetOriginOffset isVariable)
      horizontal keepPositive symbols =
      (directSourceFinalRoutedVertexPoints decider isVariable symbols).map
        (fun _ => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          (horizontalGadgetOriginOffset isVariable)) := by
  rw [directSourceFinalHeaderPointCoordinates_eq_occurrences]
  simp only [List.map_const', directSourceFinalOccurrences_length_eq_compiled, directSourceFinalRoutedVertexPoints_length]

/-- Apply padding, macrocell scaling, and the fixed gadget offset to every
compiled endpoint coordinate. -/
def directSourceFinalGadgetOriginCoordinates (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 256 keepPositive
    (fun positive => directSourceFinalRoutedVertexCoordinates decider isVariable horizontal positive symbols)
    (fun positive => directSourceFinalHeaderPointCoordinates decider
      (fun _ => horizontalGadgetOriginOffset isVariable) horizontal positive symbols)

noncomputable def directSourceFinalGadgetOriginCoordinatesComputableInPolyTime (isVariable horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGadgetOriginCoordinates decider isVariable horizontal keepPositive) := by
  unfold directSourceFinalGadgetOriginCoordinates
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 256 keepPositive
    (fun positive => directSourceFinalRoutedVertexCoordinates decider isVariable horizontal positive)
    (fun positive => directSourceFinalHeaderPointCoordinates decider (fun _ => horizontalGadgetOriginOffset isVariable) horizontal positive)
    (fun positive symbols => by rw [directSourceFinalRoutedVertexCoordinates_length, directSourceFinalRoutedVertexCoordinates_length])
    (fun positive symbols => by rw [directSourceFinalHeaderPointCoordinates_length, directSourceFinalRoutedVertexCoordinates_length])
    (fun positive => directSourceFinalRoutedVertexCoordinatesComputableInPolyTime decider isVariable horizontal positive)
    (fun positive => directSourceFinalHeaderPointCoordinatesComputableInPolyTime decider (fun _ => horizontalGadgetOriginOffset isVariable) horizontal positive)

theorem directSourceFinalGadgetOriginCoordinates_eq_affine (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalGadgetOriginCoordinates decider isVariable horizontal keepPositive symbols =
      (directSourceFinalRoutedVertexPoints decider isVariable symbols).map
        (fun point => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          (Cell.add (Cell.scale 256 point) (horizontalGadgetOriginOffset isVariable))) := by
  unfold directSourceFinalGadgetOriginCoordinates
  simp only [directSourceFinalRoutedVertexCoordinates_eq_points, constantHeaderCoordinates_eq_points, pointValue_function]
  rw [SignedUnaryCoordinateRefinement.values_map]
  apply List.map_congr_left
  intro point _
  simp only [component_affine, Nat.cast_ofNat]

/-- Actual geometric gadget origins in the same complete occurrence order. -/
def directSourceFinalHorizontalGadgetOrigins (isVariable : Bool) (symbols : List encoding.Γ) : List Cell :=
  if isVariable then
    (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
      (horizontalThreeDMVariableOriginComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))
  else horizontalPresentedClauseGadgetOrigins (PolySpaceCompiler.formulaOfSymbols decider symbols)

theorem directSourceFinalHorizontalGadgetOrigins_eq_affine (isVariable : Bool) (symbols : List encoding.Γ) :
    directSourceFinalHorizontalGadgetOrigins decider isVariable symbols =
      (directSourceFinalRoutedVertexPoints decider isVariable symbols).map
        (fun point => Cell.add (Cell.scale 256 point) (horizontalGadgetOriginOffset isVariable)) := by
  cases isVariable <;> simp only [directSourceFinalHorizontalGadgetOrigins, directSourceFinalRoutedVertexPoints,
    horizontalGadgetOriginOffset, Bool.false_eq_true, ↓reduceIte]
  · exact horizontalPresentedClauseGadgetOrigins_eq_affine (PolySpaceCompiler.formulaOfSymbols decider symbols)
  · simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro atom _
    exact horizontalThreeDMVariableOriginComputed_eq_affine _ atom

/-- Scalar coordinate fields of the actual variable or clause gadget origins. -/
def directSourceFinalHorizontalGadgetOriginCoordinates (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  (directSourceFinalHorizontalGadgetOrigins decider isVariable symbols).map
    (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive))

theorem directSourceFinalGadgetOriginCoordinates_eq_horizontal (isVariable horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalGadgetOriginCoordinates decider isVariable horizontal keepPositive symbols =
      directSourceFinalHorizontalGadgetOriginCoordinates decider isVariable horizontal keepPositive symbols := by
  rw [directSourceFinalGadgetOriginCoordinates_eq_affine, directSourceFinalHorizontalGadgetOriginCoordinates,
    directSourceFinalHorizontalGadgetOrigins_eq_affine, List.map_map]
  rfl

/-- Both complete geometric origin columns have unconditional native
polynomial-time compilers. -/
noncomputable def directSourceFinalHorizontalGadgetOriginCoordinatesComputableInPolyTime (isVariable horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalHorizontalGadgetOriginCoordinates decider isVariable horizontal keepPositive) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalGadgetOriginCoordinatesComputableInPolyTime decider isVariable horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGadgetOriginCoordinates_eq_horizontal decider isVariable horizontal keepPositive symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
