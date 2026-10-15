/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteNormalizationInputPadding
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectSparseAffineVertexRequestData

/-! # Compact vertex records commute with finite input padding -/
namespace LeanTrominoes.PeriodicCNFStripReduction
open Gadget PeriodicThreeDM PeriodicThreeDM.NormalizationCompiler

theorem sparseBoundedInputVertexRequestRecord_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertexLength : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length)
    {vertex : PeriodicThreeDMVertex} (member : vertex∈input.problem.contractedGraph.vertices)
    (bounds : let point := input.drawing.vertexPosition input.problem.incidenceGraph vertex
      0≤point.1 ∧ point.1<(input.drawing.gridSize:Int) ∧
      0≤point.2 ∧ point.2<(input.drawing.gridSize:Int)) :
    sparseBoundedInputVertexRequestRecord input.finitePad vertex=
      let point := input.drawing.vertexPosition input.problem.incidenceGraph vertex
      GadgetSparseAffineVertexTokens.record (point.1.toNat+input.drawing.gridSize)
        (2*input.drawing.gridSize-point.2.toNat-1+3*input.drawing.gridSize+2)
        (finalVertexCellType input vertex) := by
  have incidenceMember := contractedGraph_vertex_mem_incidenceGraph input.problem member
  have positionEq := PeriodicGridDrawing.finitePad_vertexPosition input.drawing
    input.problem.incidenceGraph vertexLength vertex incidenceMember
  simp only [sparseBoundedInputVertexRequestRecord,Input.finitePad_problem,
    Input.finitePad_drawing,PeriodicGridDrawing.finitePad_gridSize,positionEq,
    PeriodicGridDrawing.finitePaddingOffset,Cell.add,finalVertexCellType_finitePad input zero]
  congr 1
  · omega
  · have verticalLt : (input.drawing.vertexPosition input.problem.incidenceGraph vertex).2.toNat <
        input.drawing.gridSize := by omega
    omega
end LeanTrominoes.PeriodicCNFStripReduction
