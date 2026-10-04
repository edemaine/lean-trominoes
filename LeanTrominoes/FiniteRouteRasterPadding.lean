/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetSparseRouteComplementRequest
import LeanTrominoes.FiniteNormalizationInputPadding
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestData

/-! # Compact raster metadata for the padded finite normalization input -/
namespace LeanTrominoes.PeriodicCNFStripReduction.RouteRasterRequest
open PeriodicThreeDM PeriodicThreeDM.NormalizationCompiler

def finitePadRequest (padding : Nat) (request : Request) : Request where
  metadata :=
    { gridSize := 3*request.metadata.gridSize+1
      horizontal := request.metadata.horizontal+padding
      verticalComplement := request.metadata.verticalComplement+3*padding+2
      color := request.metadata.color }
  normalization := request.normalization

@[simp] theorem finitePadRequest_normalization (padding : Nat) (request : Request) :
    (finitePadRequest padding request).normalization=request.normalization := rfl

@[simp] theorem finitePadRequest_color (padding : Nat) (request : Request) :
    (finitePadRequest padding request).metadata.color=request.metadata.color := rfl

/-- Bounds on the original vertex allow natural-number reflection to commute
with the enlarged period and the positive padding translation. -/
theorem ofEdge_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertexLength : input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length)
    (bounds : ∀ vertex∈input.problem.contractedGraph.vertices,
      let point := input.drawing.vertexPosition input.problem.incidenceGraph vertex
      0≤point.1 ∧ point.1<(input.drawing.gridSize:Int) ∧
      0≤point.2 ∧ point.2<(input.drawing.gridSize:Int))
    {edge : ContractedEdge} (member : edge∈input.problem.contractedEdges) :
    ofEdge input.finitePad edge=finitePadRequest input.drawing.gridSize (ofEdge input edge) := by
  have contractedMember := contractedEdge_source_mem input.problem member
  have sourceMember := contractedGraph_vertex_mem_incidenceGraph input.problem contractedMember
  have pointBounds := bounds _ contractedMember
  have positionEq := PeriodicGridDrawing.finitePad_vertexPosition input.drawing
    input.problem.incidenceGraph vertexLength _ sourceMember
  have normalEq := normalizationRequest_finitePad input zero member
  unfold ofEdge finitePadRequest
  simp only [Input.finitePad_problem,Input.finitePad_drawing,PeriodicGridDrawing.finitePad_gridSize,
    positionEq,PeriodicGridDrawing.finitePaddingOffset,Cell.add]
  rw [normalEq]
  congr 2
  · omega
  · have verticalLt : (input.drawing.vertexPosition input.problem.incidenceGraph
        edge.toPeriodicEdge.source).2.toNat < input.drawing.gridSize := by omega
    omega
/-- The enlarged period leaves the padded horizontal cursor strictly inside. -/
theorem finitePadRequest_cursorValid (request : Request)
    (valid : request.metadata.CursorValid) :
    (finitePadRequest request.metadata.gridSize request).metadata.CursorValid := by
  unfold Metadata.CursorValid Metadata.cursorHorizontal Metadata.period at *
  simp only [finitePadRequest]
  omega

end LeanTrominoes.PeriodicCNFStripReduction.RouteRasterRequest
