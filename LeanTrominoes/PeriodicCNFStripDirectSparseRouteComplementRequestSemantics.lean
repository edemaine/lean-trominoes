/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteComplementRequest
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestData

/-! # Complement-counter semantics for direct sparse route requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace RouteRasterRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteComplementRequestSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every direct route request starts strictly inside its unary period.
Consequently its horizontal coordinate admits the complementary-counter
representation used by the low-level route machine. -/
theorem directSparse_ofEdge_cursorValid
    (symbols : List encoding.Γ)
    {edge : PeriodicThreeDM.ContractedEdge}
    (member : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    (ofEdge input edge).metadata.CursorValid := by
  dsimp only
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  change (ofEdge input edge).metadata.CursorValid
  have sourceMember :
      edge.toPeriodicEdge.source ∈ input.problem.contractedGraph.vertices :=
    contractedEdge_source_mem input.problem member
  have bounds := directSparseComputedInput_vertexPosition_bounds
    decider symbols sourceMember
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
  have horizontalToNatLt : horizontal.toNat < input.drawing.gridSize := by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg bounds.1]
    exact bounds.2.1
  unfold ofEdge Metadata.CursorValid Metadata.cursorHorizontal Metadata.period
  simp only [positionEq]
  omega

/-- The complement-counter interpretation of a direct edge request emits
the exact canonical raster-direction record block. -/
theorem directSparse_complementRecordBlock_ofEdge
    (symbols : List encoding.Γ)
    {edge : PeriodicThreeDM.ContractedEdge}
    (member : edge ∈
      (directSparseComputedNormalizationInputOfSymbols
        decider symbols).problem.contractedEdges) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    complementRecordBlock (ofEdge input edge) =
      PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock
        input edge := by
  dsimp only
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  change complementRecordBlock (ofEdge input edge) =
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock
      input edge
  rw [complementRecordBlock_eq_normalizedRecordBlock
    (ofEdge input edge)
    (directSparse_ofEdge_cursorValid decider symbols member)]
  exact directSparse_normalizedRecordBlock_ofEdge decider symbols member

/-- Interpreting the complete direct request list through complementary
horizontal counters gives the exact direct raster-cursor target. -/
theorem directSparseRouteComplementRequestBlocks_eq
    (symbols : List encoding.Γ) :
    (directSparseRouteRasterRequestsOfSymbols decider symbols).flatMap
        complementRecordBlock =
      directSparseComputedRouteRasterDirectionRecordsOfSymbols
        decider symbols := by
  unfold directSparseRouteRasterRequestsOfSymbols
    directSparseComputedRouteRasterDirectionRecordsOfSymbols
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro edge member
  exact directSparse_complementRecordBlock_ofEdge decider symbols member

end RouteRasterRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
