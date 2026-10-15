/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionPointLookup
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingUnitSubdivision

/-! # The absolute subdivision-node coordinates reproduce the moved polygonal route -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def globalPoint {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (entry : Vertex V × Cell) : Cell :=
  Cell.add (position source drawing factor entry.1) (Cell.scale ((factor:Int)*drawing.gridSize) entry.2)

theorem internalPoints_fst (drawing : PeriodicGridDrawing) (index : Nat) :
    (internalPoints drawing index).map Prod.fst=(drawing.edgeRoute index).tail.dropLast := by
  exact List.zipIdx_map_fst _ _

theorem middle_globalPoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (tagged : PeriodicEdge V × Nat) :
    (middle drawing factor tagged).map (globalPoint source drawing factor)=
      (drawing.edgeRoute tagged.2).tail.dropLast.map (InteriorBends.point drawing.gridSize factor) := by
  rw [middle,List.map_map]
  have mapped : (internalPoints drawing tagged.2).map
      (fun entry => globalPoint source drawing factor
        (Vertex.bend tagged.2 entry.2,InteriorBends.cell drawing.gridSize factor entry.1))=
      (internalPoints drawing tagged.2).map (fun entry => InteriorBends.point drawing.gridSize factor entry.1) := by
    apply List.map_congr_left
    intro entry member
    simp only [globalPoint,position_middle source drawing factor tagged member]
    exact (InteriorBends.point_decomposition _ _ _).symm
  change (internalPoints drawing tagged.2).map
      (fun entry => globalPoint source drawing factor
        (Vertex.bend tagged.2 entry.2,InteriorBends.cell drawing.gridSize factor entry.1))= _
  rw [mapped]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (List.map (InteriorBends.point drawing.gridSize factor)) (internalPoints_fst drawing tagged.2)

theorem nodes_globalPoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) (factor : Nat)
    {tagged : PeriodicEdge V × Nat} (member : tagged∈source.edges.zipIdx) :
    (nodes tagged (middle drawing factor tagged)).map (globalPoint source drawing factor)=
      (drawing.edgeRoute tagged.2).map (InteriorBends.point drawing.gridSize factor) := by
  have endpoints := planar.1.1.2.2.2.2.2 tagged member
  have vertices := planar.1.1.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have sourceBounds := planar.1.1.2.2.2.2.1 _ (planar.1.1.vertexPosition_mem vertices.1)
  have targetBounds := planar.1.1.2.2.2.2.1 _ (planar.1.1.vertexPosition_mem vertices.2)
  have routeMember := edgeRoute_mem_of_compatible planar.1.1 member
  have reconstructed := route_eq_endpoints_and_internal (planar.1.2.1 _ routeMember).1 endpoints.1 endpoints.2
  rw [nodes,List.map_append,List.map_cons,List.map_cons,List.map_nil,middle_globalPoints]
  change (Cell.add (Cell.scale factor (drawing.vertexPosition source tagged.1.source))
      (Cell.scale ((factor:Int)*drawing.gridSize) (0,0))::
      (drawing.edgeRoute tagged.2).tail.dropLast.map (InteriorBends.point drawing.gridSize factor))++
      [Cell.add (Cell.scale factor (drawing.vertexPosition source tagged.1.target))
        (Cell.scale ((factor:Int)*drawing.gridSize) tagged.1.offset)] = _
  have firstEq : Cell.add (Cell.scale factor (drawing.vertexPosition source tagged.1.source))
      (Cell.scale ((factor:Int)*drawing.gridSize) (0,0))=
      InteriorBends.point drawing.gridSize factor (drawing.vertexPosition source tagged.1.source) := by
    simp only [InteriorBends.point_interior sourceBounds,Cell.add,Cell.scale,mul_zero,add_zero]
  have lastEq := InteriorBends.point_translated_interior (factor := (factor:Int)) targetBounds tagged.1.offset
  rw [firstEq,← lastEq]
  simpa only [List.map_append,List.map_cons,List.map_nil,periodTranslation] using
    (congrArg (List.map (InteriorBends.point drawing.gridSize factor)) reconstructed).symm

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
