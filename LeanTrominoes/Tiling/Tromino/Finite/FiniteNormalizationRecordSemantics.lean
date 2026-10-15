/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectSparseRouteRasterRequestData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectSparseRouteRecordData

/-! # Source-independent semantics of compact normalization records -/
namespace LeanTrominoes.PeriodicCNFStripReduction.RouteRasterRequest
open Gadget PeriodicThreeDM PeriodicThreeDM.NormalizationCompiler
open PeriodicThreeDM.NormalizationDirectionRequest

theorem ofEdge_location_eq (input : Input) {edge : ContractedEdge}
    (member : edge∈input.problem.contractedEdges)
    (bounds : let position := input.drawing.vertexPosition input.problem.incidenceGraph edge.toPeriodicEdge.source
      0≤position.1 ∧ position.1<(input.drawing.gridSize:Int) ∧
      0≤position.2 ∧ position.2<(input.drawing.gridSize:Int)) :
    (ofEdge input edge).metadata.location=
      stripRasterLocation (finalNormalizationPeriod input)
        (finalNormalizationPosition input edge.toPeriodicEdge.source) := by
  have sourceMember := contractedEdge_source_mem input.problem member
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

/-- Compact requests render the exact route assignment words of any bounded
normalization input satisfying the route-direction conditions. -/
theorem normalizedRecordBlock_ofEdge (input : Input) {edge : ContractedEdge}
    (member : edge∈input.problem.contractedEdges)
    (bounds : let position := input.drawing.vertexPosition input.problem.incidenceGraph edge.toPeriodicEdge.source
      0≤position.1 ∧ position.1<(input.drawing.gridSize:Int) ∧
      0≤position.2 ∧ position.2<(input.drawing.gridSize:Int))
    (conditions : RouteDirectionConditions input edge) :
    normalizedRecordBlock (ofEdge input edge)=sparseRouteRecordBlock input edge := by
  have periodEq : (ofEdge input edge).metadata.period=finalNormalizationPeriod input := by
    unfold ofEdge Metadata.period
    rw [normalizationCompiler_finalNormalizationPeriod_eq_scaleCube]
  have directionsEq : (normalizeThreeRounds (ofEdge input edge).normalization).directions=
      finalNormalizationRouteDirections input edge :=
    NormalizationDirectionRequest.normalizeThreeRounds_ofEdge_directions input edge
  have rasterEq : normalizedRecordBlock (ofEdge input edge)=
      finalNormalizationRouteRasterDirectionRecordBlock input edge := by
    unfold normalizedRecordBlock finalNormalizationRouteRasterDirectionRecordBlock
    rw [periodEq,ofEdge_location_eq input member bounds,directionsEq]
    rfl
  rw [rasterEq,finalNormalizationRouteRasterDirectionRecordBlock_eq,
    ←finalNormalizationRouteRecordBlock_eq_directions input edge conditions,
    ←sparseRouteRecordBlock_eq_tripleBlocks]
end LeanTrominoes.PeriodicCNFStripReduction.RouteRasterRequest
