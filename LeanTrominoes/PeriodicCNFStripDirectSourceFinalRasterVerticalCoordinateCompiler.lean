/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectDrawingGridUnitEmitter
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRasterHorizontalCoordinateCompiler
import LeanTrominoes.UnaryFieldUnitLengthBroadcastCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryFieldConstantOffsetCompiler
import LeanTrominoes.UnaryAlignedDifferenceCompiler

/-! # Actual grid and vertical-complement raster fields from source symbols -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing

private theorem reflectedValues (grid : Nat) (vertical : List Nat) :
    UnaryAlignedDifference.values true
        (UnaryFieldConstantScale.values 2 (vertical.map (fun _ => grid)))
        (UnaryFieldConstantOffsets.values 1 vertical) =
      vertical.map (fun value => 2 * grid - value - 1) := by
  rw [UnaryAlignedDifference.values_eq_zipWith]
  unfold UnaryFieldConstantScale.values UnaryFieldConstantOffsets.values
  simp only [List.map_map, Function.comp_def]
  induction vertical with
  | nil => rfl
  | cons value vertical induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, ↓reduceIte]
      congr 1
      omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- One copy of the actual drawing grid size for every contracted route. -/
def directSourceFinalRasterGridSizes (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldUnitLengthBroadcast.values
    (directSourceFinalContractedSourceCoordinates decider false true symbols)
    (directDrawingGridUnitsOfSymbols decider symbols)

noncomputable def directSourceFinalRasterGridSizesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRasterGridSizes decider) := by
  unfold directSourceFinalRasterGridSizes
  exact UnaryFieldUnitLengthBroadcast.nativeListComputableInPolyTime _ _
    (directSourceFinalContractedSourceCoordinatesComputableInPolyTime decider false true)
    (directDrawingGridUnitsOfSymbolsComputableInPolyTime decider)

theorem directSourceFinalRasterGridSizes_eq_map (symbols : List encoding.Γ) :
    directSourceFinalRasterGridSizes decider symbols =
      (directSourceFinalContractedSourceCoordinates decider false true symbols).map
        (fun _ => (directSparseComputedNormalizationInputOfSymbols decider symbols).drawing.gridSize) := by
  unfold directSourceFinalRasterGridSizes
  rw [UnaryFieldUnitLengthBroadcast.values_eq_map, directDrawingGridUnitsOfSymbols_length]

@[simp] theorem directSourceFinalRasterGridSizes_length (symbols : List encoding.Γ) :
    (directSourceFinalRasterGridSizes decider symbols).length =
      (directSourceFinalContractedSourceCoordinates decider false true symbols).length := by
  rw [directSourceFinalRasterGridSizes_eq_map, List.length_map]

theorem directSourceFinalRasterGridSizes_eq_raster (symbols : List encoding.Γ) :
    directSourceFinalRasterGridSizes decider symbols =
      (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.gridSize) := by
  rw [directSourceFinalRasterGridSizes_eq_map,
    directSourceFinalContractedSourceCoordinates_eq_input]
  unfold RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro edge _
  rfl

/-- Subtract the route's vertical coordinate and one from twice its grid size. -/
def directSourceFinalRasterVerticalComplements (symbols : List encoding.Γ) : List Nat :=
  UnaryAlignedDifference.values true
    (UnaryFieldConstantScale.values 2 (directSourceFinalRasterGridSizes decider symbols))
    (UnaryFieldConstantOffsets.values 1
      (directSourceFinalContractedSourceCoordinates decider false true symbols))

noncomputable def directSourceFinalRasterVerticalComplementsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRasterVerticalComplements decider) := by
  unfold directSourceFinalRasterVerticalComplements
  exact UnaryAlignedDifference.nativeListComputableInPolyTime true _ _
    (fun symbols => by
      simp only [UnaryFieldConstantScale.values, UnaryFieldConstantOffsets.values,
        List.length_map, directSourceFinalRasterGridSizes_length])
    (TM2CompositionMachine.computableInPolyTime
      (directSourceFinalRasterGridSizesComputableInPolyTime decider)
      (UnaryFieldConstantScale.computableInPolyTime 2))
    (TM2CompositionMachine.computableInPolyTime
      (directSourceFinalContractedSourceCoordinatesComputableInPolyTime decider false true)
      (UnaryFieldConstantOffsets.computableInPolyTime 1))

theorem directSourceFinalRasterVerticalComplements_eq_raster (symbols : List encoding.Γ) :
    directSourceFinalRasterVerticalComplements decider symbols =
      (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.verticalComplement) := by
  unfold directSourceFinalRasterVerticalComplements
  rw [directSourceFinalRasterGridSizes_eq_map, reflectedValues,
    directSourceFinalContractedSourceCoordinates_reflected_eq_raster_vertical]

/-- The actual grid-size field column has an unconditional native compiler. -/
noncomputable def directSourceFinalRasterGridFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.gridSize)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalRasterGridSizesComputableInPolyTime decider)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRasterGridSizes_eq_raster decider symbols))

/-- The actual reflected vertical field column has an unconditional native compiler. -/
noncomputable def directSourceFinalRasterVerticalFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.verticalComplement)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalRasterVerticalComplementsComputableInPolyTime decider)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalRasterVerticalComplements_eq_raster decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction
end
