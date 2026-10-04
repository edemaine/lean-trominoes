/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNormalizationInputPadding

/-! # Fundamental-square vertex bounds for the padded compiler input -/
namespace LeanTrominoes.PeriodicThreeDM.NormalizationCompiler

theorem Input.finitePad_vertexPosition_bounds (input : Input)
    (lengthEq : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length)
    {vertex : PeriodicThreeDMVertex} (member : vertex∈input.problem.contractedGraph.vertices)
    (bounds : let point := input.drawing.vertexPosition input.problem.incidenceGraph vertex
      0≤point.1 ∧ point.1<(input.drawing.gridSize:Int) ∧
      0≤point.2 ∧ point.2<(input.drawing.gridSize:Int)) :
    let point := input.finitePad.drawing.vertexPosition input.finitePad.problem.incidenceGraph vertex
    0≤point.1 ∧ point.1<(input.finitePad.drawing.gridSize:Int) ∧
      0≤point.2 ∧ point.2<(input.finitePad.drawing.gridSize:Int) := by
  have positionEq := PeriodicGridDrawing.finitePad_vertexPosition input.drawing
    input.problem.incidenceGraph lengthEq vertex (contractedGraph_vertex_mem_incidenceGraph input.problem member)
  simp only [Input.finitePad_problem,Input.finitePad_drawing,positionEq,
    PeriodicGridDrawing.finitePad_gridSize,PeriodicGridDrawing.finitePaddingOffset,Cell.add]
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega
end LeanTrominoes.PeriodicThreeDM.NormalizationCompiler
