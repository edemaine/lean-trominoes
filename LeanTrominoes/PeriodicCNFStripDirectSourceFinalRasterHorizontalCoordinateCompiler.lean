/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalContractedSourceCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestData

/-! # Actual horizontal raster-request fields from source symbols -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

private theorem horizontalField_ofEdge (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (edge : PeriodicThreeDM.ContractedEdge) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools true true)
        (input.drawing.vertexPosition input.problem.incidenceGraph edge.toPeriodicEdge.source) =
      (RouteRasterRequest.ofEdge input edge).metadata.horizontal := by
  rfl

private theorem verticalField_ofEdge (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (edge : PeriodicThreeDM.ContractedEdge) :
    2 * input.drawing.gridSize -
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools false true)
          (input.drawing.vertexPosition input.problem.incidenceGraph edge.toPeriodicEdge.source) - 1 =
      (RouteRasterRequest.ofEdge input edge).metadata.verticalComplement := by
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled coordinates belong to the normalization input consumed by
the actual raster request list. -/
theorem directSourceFinalContractedSourceCoordinates_eq_input
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalContractedSourceCoordinates decider horizontal keepPositive symbols =
      (directSparseComputedNormalizationInputOfSymbols decider symbols).problem.contractedEdges.map
        (fun edge => CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          ((directSparseComputedNormalizationInputOfSymbols decider symbols).drawing.vertexPosition
            (directSparseComputedNormalizationInputOfSymbols decider symbols).problem.incidenceGraph
              edge.toPeriodicEdge.source)) := by
  rw [directSourceFinalContractedSourceCoordinates_eq_horizontal]
  rfl

/-- The positive horizontal column is exactly the canonical raster header field. -/
theorem directSourceFinalContractedSourceCoordinates_eq_raster_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalContractedSourceCoordinates decider true true symbols =
      (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.horizontal) := by
  rw [directSourceFinalContractedSourceCoordinates_eq_input]
  unfold RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
  rw [List.map_map]
  apply List.map_congr_left
  intro edge _
  exact horizontalField_ofEdge _ edge

/-- The genuine horizontal field stream has an unconditional native compiler. -/
noncomputable def directSourceFinalRasterHorizontalCoordinatesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.horizontal)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalContractedSourceCoordinatesComputableInPolyTime decider true true)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalContractedSourceCoordinates_eq_raster_horizontal decider symbols))

/-- Grid reflection of the positive vertical column is the canonical vertical
header field. The grid broadcast and subtraction compilers can use this equation. -/
theorem directSourceFinalContractedSourceCoordinates_reflected_eq_raster_vertical
    (symbols : List encoding.Γ) :
    (directSourceFinalContractedSourceCoordinates decider false true symbols).map
        (fun vertical => 2 * (directSparseComputedNormalizationInputOfSymbols decider symbols).drawing.gridSize - vertical - 1) =
      (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.verticalComplement) := by
  rw [directSourceFinalContractedSourceCoordinates_eq_input]
  unfold RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro edge _
  exact verticalField_ofEdge _ edge

end LeanTrominoes.PeriodicCNFStripReduction
end
