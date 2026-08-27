/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterDirectionData
import LeanTrominoes.GadgetSparseRouteRasterRequestData

/-! # Compact raster requests for direct sparse routes

One route request retains only three unary base quantities: the original
grid size and the source vertex's original horizontal and reflected-vertical
indices.  Fixed affine interpretation supplies the final factor `1728` and
the two source offsets.  The remaining fields are finite.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace RouteRasterRequest

open Gadget
open PeriodicThreeDM.NormalizationDirectionRequest

/-- Compact request extracted from one executable normalization edge. -/
def ofEdge (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (edge : PeriodicThreeDM.ContractedEdge) : Request :=
  let source := edge.toPeriodicEdge.source
  let position := input.drawing.vertexPosition
    input.problem.incidenceGraph source
  { metadata :=
      { gridSize := input.drawing.gridSize
        horizontal := position.1.toNat
        verticalComplement :=
          2 * input.drawing.gridSize - position.2.toNat - 1
        color := edge.color }
    normalization :=
      PeriodicThreeDM.NormalizationDirectionRequest.ofEdge input edge }

/-- Every listed contracted edge has its source in the contracted vertex
list. -/
theorem contractedEdge_source_mem
    (problem : PeriodicThreeDM)
    {edge : PeriodicThreeDM.ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge.toPeriodicEdge.source ∈ problem.contractedGraph.vertices := by
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges := by
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  exact (problem.contractedGraph_isWellFormed.2
    edge.toPeriodicEdge graphEdgeMember).1

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteRasterRequestDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- On every direct edge, compact affine metadata denotes the exact
rasterized final source location. -/
theorem directSparse_ofEdge_location_eq
    (symbols : List encoding.Γ)
    {edge : PeriodicThreeDM.ContractedEdge}
    (member : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    (ofEdge input edge).metadata.location =
      PeriodicThreeDM.stripRasterLocation
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod input)
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPosition
          input edge.toPeriodicEdge.source) := by
  dsimp only
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  change (ofEdge input edge).metadata.location =
    PeriodicThreeDM.stripRasterLocation
      (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod input)
      (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPosition
        input edge.toPeriodicEdge.source)
  have sourceMember :
      edge.toPeriodicEdge.source ∈ input.problem.contractedGraph.vertices :=
    contractedEdge_source_mem input.problem member
  have bounds := directSparseComputedInput_vertexPosition_bounds
    decider symbols sourceMember
  rw [normalizationCompiler_finalNormalizationPosition_eq_scaleCube]
  rw [normalizationCompiler_finalNormalizationPeriod_eq_scaleCube]
  rw [normalizationCompiler_normalizationPosition0_eq_inputDrawing
    input sourceMember]
  rcases positionEq : input.drawing.vertexPosition
      input.problem.incidenceGraph edge.toPeriodicEdge.source with
    ⟨horizontal, vertical⟩
  change
    (let position := input.drawing.vertexPosition
      input.problem.incidenceGraph edge.toPeriodicEdge.source
    0 ≤ position.1 ∧
      position.1 < (input.drawing.gridSize : Int) ∧
      0 ≤ position.2 ∧
      position.2 < (input.drawing.gridSize : Int)) at bounds
  dsimp only at bounds
  rw [positionEq] at bounds
  simp only at bounds
  have horizontalNonnegative : 0 ≤ horizontal := by
    exact bounds.1
  have horizontalLt : horizontal < (input.drawing.gridSize : Int) := by
    exact bounds.2.1
  have verticalNonnegative : 0 ≤ vertical := by
    exact bounds.2.2.1
  have verticalLt : vertical < (input.drawing.gridSize : Int) := by
    exact bounds.2.2.2
  have verticalToNatLt : vertical.toNat < input.drawing.gridSize := by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg verticalNonnegative]
    exact verticalLt
  have verticalToNatLeDouble :
      vertical.toNat ≤ 2 * input.drawing.gridSize := by
    omega
  have oneLeComplement :
      1 ≤ 2 * input.drawing.gridSize - vertical.toNat := by
    omega
  have complementCast :
      ((2 * input.drawing.gridSize - vertical.toNat - 1 : Nat) : Int) =
        2 * (input.drawing.gridSize : Int) - vertical - 1 := by
    rw [Nat.cast_sub oneLeComplement,
      Nat.cast_sub verticalToNatLeDouble]
    push_cast
    rw [Int.toNat_of_nonneg verticalNonnegative]
  simp only [ofEdge, Metadata.location, positionEq]
  simp only [Cell.scale, Cell.add,
    PeriodicThreeDM.stripRasterLocation, Prod.mk.injEq]
  constructor
  · push_cast
    rw [Int.toNat_of_nonneg horizontalNonnegative]
    symm
    apply Int.emod_eq_of_lt
    · omega
    · omega
  · push_cast
    rw [complementCast]
    ring

/-- A compact direct edge request emits its exact raster-cursor record
block after normalization. -/
theorem directSparse_normalizedRecordBlock_ofEdge
    (symbols : List encoding.Γ)
    {edge : PeriodicThreeDM.ContractedEdge}
    (member : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    normalizedRecordBlock (ofEdge input edge) =
      PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock
        input edge := by
  dsimp only
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  change normalizedRecordBlock (ofEdge input edge) =
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock
      input edge
  have periodEq :
      (ofEdge input edge).metadata.period =
        PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod
          input := by
    unfold ofEdge Metadata.period
    rw [normalizationCompiler_finalNormalizationPeriod_eq_scaleCube]
  have colorEq : (ofEdge input edge).metadata.color = edge.color := by
    rfl
  have directionsEq :
      (normalizeThreeRounds (ofEdge input edge).normalization).directions =
        PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteDirections
          input edge := by
    exact
      PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds_ofEdge_directions
        input edge
  unfold normalizedRecordBlock
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock
  rw [periodEq, colorEq,
    directSparse_ofEdge_location_eq decider symbols member,
    directionsEq]

/-- Canonical compact request list in contracted-edge order. -/
def directSparseRouteRasterRequestsOfSymbols
    (symbols : List encoding.Γ) : List Request :=
  let input := directSparseComputedNormalizationInputOfSymbols decider symbols
  input.problem.contractedEdges.map (ofEdge input)

/-- Interpreting all compact requests gives the exact direct raster-cursor
target. -/
theorem directSparseRouteRasterRequestBlocks_eq
    (symbols : List encoding.Γ) :
    (directSparseRouteRasterRequestsOfSymbols decider symbols).flatMap
        normalizedRecordBlock =
      directSparseComputedRouteRasterDirectionRecordsOfSymbols
        decider symbols := by
  unfold directSparseRouteRasterRequestsOfSymbols
    directSparseComputedRouteRasterDirectionRecordsOfSymbols
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro edge member
  exact directSparse_normalizedRecordBlock_ofEdge decider symbols member

end RouteRasterRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
