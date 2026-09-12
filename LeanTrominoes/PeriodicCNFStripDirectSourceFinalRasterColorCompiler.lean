/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalContractedSourceCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestData
import LeanTrominoes.UnaryFieldConstantTableCompiler
import LeanTrominoes.FiniteIndexSlotUnaryDecoderCompiler

/-! # Actual contracted-route raster colors from source symbols -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing Gadget PeriodicThreeDM PeriodicCNF

local instance : Inhabited WireColor := ⟨.red⟩

private def rasterColorCode : WireColor → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

private def rasterColorOfSlot (pair : FiniteIndexSlotUnaryDecoder.Pair 1) : WireColor :=
  if pair.2.val = 0 then .red else if pair.2.val = 1 then .green else .blue

private theorem rasterColor_decode (color : WireColor) :
    rasterColorOfSlot (FiniteIndexSlotUnaryDecoder.boundedCode 1 (rasterColorCode color)) = color := by
  cases color <;> rfl

private theorem incidenceTags_colorCodes (problem : PeriodicThreeDM) :
    problem.incidenceTags.map (fun tag => rasterColorCode tag.color) =
      (List.range problem.triples.length).flatMap (fun _ => [0, 1, 2]) := by
  rw [incidenceTags_eq_range_flatMap, List.map_flatMap]
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Emit the RGB code table once per actual triple. -/
def directSourceFinalIncidenceColorCodes (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantTable.values [0, 1, 2]
    (directSourceFinalTripleCoordinates decider true true symbols)

noncomputable def directSourceFinalIncidenceColorCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalIncidenceColorCodes decider) := by
  unfold directSourceFinalIncidenceColorCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalTripleCoordinatesComputableInPolyTime decider true true)
    (UnaryFieldConstantTable.computableInPolyTime [0, 1, 2])

private theorem incidenceColorCodes_eq (symbols : List encoding.Γ) :
    directSourceFinalIncidenceColorCodes decider symbols =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
        (fun tag => rasterColorCode tag.color) := by
  have aligned : (directSourceFinalTripleCoordinates decider true true symbols).length =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).triples.length := by
    rw [directSourceFinalTripleCoordinates_length, ← horizontalThreeDMPositionProblemComputed_eq]
    exact horizontalThreeDMTriplePositionsComputed_length _
  rw [incidenceTags_colorCodes]
  simp [directSourceFinalIncidenceColorCodes, UnaryFieldConstantTable.values,
    List.flatMap_def, aligned]

/-- Select RGB codes at exactly the source incidences of contracted edges. -/
def directSourceFinalContractedColorCodes (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldBooleanFilter.selectedValues
    (CountedContractedIncidence.sourceControls (directSourceFinalCanonicalElementDegrees decider symbols))
    (directSourceFinalSelectedIncidenceValues decider symbols
      (directSourceFinalIncidenceColorCodes decider symbols))

noncomputable def directSourceFinalContractedColorCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalContractedColorCodes decider) := by
  unfold directSourceFinalContractedColorCodes
  exact UnaryFieldBooleanFilter.selectedValuesNativeListComputableInPolyTime _ _
    (TM2CompositionMachine.computableInPolyTime
      (directSourceFinalCanonicalElementDegreesComputableInPolyTime decider)
      CountedContractedIncidence.sourceControlsComputableInPolyTime)
    (directSourceFinalSelectedIncidenceValuesComputableInPolyTime decider _
      (fun symbols => by rw [incidenceColorCodes_eq, List.length_map])
      (directSourceFinalIncidenceColorCodesComputableInPolyTime decider))

private theorem contractedColorCodes_eq (symbols : List encoding.Γ) :
    directSourceFinalContractedColorCodes decider symbols =
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.map
        (fun edge => rasterColorCode edge.color) := by
  unfold directSourceFinalContractedColorCodes
  rw [incidenceColorCodes_eq, directSourceFinalSelectedIncidenceValues_map_eq_horizontal,
    directSourceFinalCanonicalElementDegrees_eq_horizontal,
    CountedContractedIncidence.selected_sources_eq_contracted
      (horizontalThreeDMProblemComputed (PolySpaceCompiler.formulaOfSymbols decider symbols))
      (fun tag : IncidenceTag => rasterColorCode tag.color) (by
        rw [horizontalThreeDMProblemComputed_eq_problem]
        exact problem_degreeTwoOrThree _)]
  apply List.map_congr_left
  intro edge _
  cases edge <;> rfl

/-- Decode the compiled finite RGB fields. -/
def directSourceFinalRasterColors (symbols : List encoding.Γ) : List WireColor :=
  (FiniteIndexSlotUnaryDecoder.pairs 1 (directSourceFinalContractedColorCodes decider symbols)).map rasterColorOfSlot

noncomputable def directSourceFinalRasterColorsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalRasterColors decider) := by
  let decoded := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalContractedColorCodesComputableInPolyTime decider)
    (FiniteIndexSlotUnaryDecoder.computableInPolyTime 1)
  let projected := TM2CompositionMachine.computableInPolyTime decoded
    (FiniteBlockTransducer.computableInPolyTime (fun pair => [rasterColorOfSlot pair]))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq projected (fun symbols => by
    unfold directSourceFinalRasterColors
    rw [← List.map_eq_flatMap])

theorem directSourceFinalRasterColors_eq_raster (symbols : List encoding.Γ) :
    directSourceFinalRasterColors decider symbols =
      (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.color) := by
  unfold directSourceFinalRasterColors FiniteIndexSlotUnaryDecoder.pairs
  rw [contractedColorCodes_eq]
  simp only [List.map_map, Function.comp_def, rasterColor_decode]
  change (directSparseComputedNormalizationInputOfSymbols decider symbols).problem.contractedEdges.map
      (fun edge => edge.color) = _
  unfold RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
  rw [List.map_map]
  apply List.map_congr_left
  intro edge _
  rfl

/-- The canonical raster color stream has an unconditional native compiler. -/
noncomputable def directSourceFinalRasterColorFieldsComputableInPolyTime :
    @TM2ComputableInPolyTime (List encoding.Γ) (List WireColor) encoding.Γ WireColor id id
      (fun symbols => (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.color)) := by
  have equal : directSourceFinalRasterColors decider =
      (fun symbols => (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols decider symbols).map
        (fun request => request.metadata.color)) :=
    funext (directSourceFinalRasterColors_eq_raster decider)
  rw [← equal]
  exact directSourceFinalRasterColorsComputableInPolyTime decider

end LeanTrominoes.PeriodicCNFStripReduction
end
