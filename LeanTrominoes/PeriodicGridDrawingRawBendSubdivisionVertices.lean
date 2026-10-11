/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivision
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionMembership
import LeanTrominoes.PeriodicGridDrawingPolygonalPointOccurrences

/-! # Distinct raw bend positions, including boundary representatives

Original planarity isolates every internal listed point from vertices and
from all other bend occurrences. Taking residues therefore preserves the
injectivity of the subdivision's vertex positions without perturbation.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

theorem subdivision_vertices_eq {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    (subdivisionGraph source drawing).vertices = (BendSubdivision.subdivisionGraph source drawing 1).vertices := by
  simp only [subdivisionGraph,BendSubdivision.subdivisionGraph,graph,middle,BendSubdivision.middle,
    List.map_map,Function.comp_def]

theorem original_vertex_mem {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {vertex : V} :
    Vertex.original vertex ∈ (subdivisionGraph source drawing).vertices ↔ vertex ∈ source.vertices := by
  rw [subdivision_vertices_eq]
  exact BendSubdivision.original_vertex_mem

theorem bend_vertex_mem_bounds {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible source) {edgeIndex pointIndex : Nat}
    (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    edgeIndex < drawing.edgeRoutes.length ∧ 0 < pointIndex ∧ pointIndex+1 < (drawing.edgeRoute edgeIndex).length := by
  rw [subdivision_vertices_eq] at member
  exact BendSubdivision.bend_vertex_mem_bounds compatible member

def bendCopy (drawing : PeriodicGridDrawing) (edgeIndex pointIndex : Nat) : Cell :=
  Cell.scale (-1) (cell drawing.gridSize ((drawing.edgeRoute edgeIndex).getD pointIndex (0,0)))

theorem bend_lifted_position {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {edgeIndex pointIndex : Nat}
    (valid : pointIndex+1 < (drawing.edgeRoute edgeIndex).length) :
    Cell.add (drawing.periodTranslation (bendCopy drawing edgeIndex pointIndex))
      (drawing.edgeRoute edgeIndex)[pointIndex] = position source drawing (.bend edgeIndex pointIndex) := by
  have pointValid : pointIndex < (drawing.edgeRoute edgeIndex).length := by omega
  simp only [bendCopy,position,List.getD_eq_getElem _ _ pointValid,periodTranslation,cell,representative,Cell.add,Cell.scale]
  apply Prod.ext <;> dsimp
  · nlinarith [Int.emod_add_mul_ediv ((drawing.edgeRoute edgeIndex)[pointIndex]).1 (drawing.gridSize : Int)]
  · nlinarith [Int.emod_add_mul_ediv ((drawing.edgeRoute edgeIndex)[pointIndex]).2 (drawing.gridSize : Int)]

theorem bend_position_ne_original {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {edgeIndex pointIndex : Nat} {vertex : V}
    (bendMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices)
    (originalMember : Vertex.original vertex ∈ (subdivisionGraph source drawing).vertices) :
    position source drawing (.bend edgeIndex pointIndex) ≠ position source drawing (.original vertex) := by
  have bounds := bend_vertex_mem_bounds planar.1.1 bendMember
  have different := internal_route_point_avoids_vertex planar bounds.1 bounds.2.1 bounds.2.2
    (planar.1.1.vertexPosition_mem (original_vertex_mem.mp originalMember))
    (bendCopy drawing edgeIndex pointIndex) (0,0)
  rw [bend_lifted_position source drawing bounds.2.2] at different
  simpa only [position,periodTranslation,Cell.scale,mul_zero,Cell.add,add_zero] using different

theorem bend_positions_injective {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    {firstEdge firstPoint secondEdge secondPoint : Nat}
    (firstMember : Vertex.bend firstEdge firstPoint ∈ (subdivisionGraph source drawing).vertices)
    (secondMember : Vertex.bend secondEdge secondPoint ∈ (subdivisionGraph source drawing).vertices)
    (equal : position source drawing (.bend firstEdge firstPoint) = position source drawing (.bend secondEdge secondPoint)) :
    (firstEdge,firstPoint) = (secondEdge,secondPoint) := by
  have firstBounds := bend_vertex_mem_bounds planar.1.1 firstMember
  have secondBounds := bend_vertex_mem_bounds planar.1.1 secondMember
  have coordinates := (bend_lifted_position source drawing firstBounds.2.2).trans
    (equal.trans (bend_lifted_position source drawing secondBounds.2.2).symm)
  have keys := internal_route_point_occurrences_unique planar firstBounds.1 secondBounds.1
    firstBounds.2.1 secondBounds.2.1 firstBounds.2.2 secondBounds.2.2
    (bendCopy drawing firstEdge firstPoint) (bendCopy drawing secondEdge secondPoint) coordinates
  exact Prod.ext (congrArg (fun key : Nat × Nat × Cell => key.1) keys)
    (congrArg (fun key : Nat × Nat × Cell => key.2.1) keys)

theorem subdivision_vertexPositions_nodup {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) :
    (subdivisionDrawing source drawing).vertexPositions.Nodup := by
  apply (subdivisionGraph_wellFormed planar.1.1.1 drawing).1.map_on
  intro first firstMember second secondMember equal
  cases first with
  | original first =>
      cases second with
      | original second => exact congrArg Vertex.original (planar.1.1.vertexPosition_injective_on
          (original_vertex_mem.mp firstMember) (original_vertex_mem.mp secondMember) equal)
      | bend edgeIndex pointIndex => exact (bend_position_ne_original planar secondMember firstMember equal.symm).elim
  | bend firstEdge firstPoint =>
      cases second with
      | original second => exact (bend_position_ne_original planar firstMember secondMember equal).elim
      | bend secondEdge secondPoint =>
          have indices := bend_positions_injective planar firstMember secondMember equal
          have edgeEq : firstEdge = secondEdge := congrArg Prod.fst indices
          have pointEq : firstPoint = secondPoint := congrArg Prod.snd indices
          rw [edgeEq,pointEq]

theorem shifted_vertexPositions_nodup {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source) :
    (shiftedDrawing source drawing).vertexPositions.Nodup := by
  have mapped := (subdivision_vertexPositions_nodup planar).map
    (f := fun point => Cell.add (1,1) (Cell.scale 2 point)) (by
      intro first second equal
      have x := congrArg Prod.fst equal
      have y := congrArg Prod.snd equal
      apply Prod.ext <;> simp only [Cell.add,Cell.scale] at x y <;> omega)
  change ((subdivisionGraph source drawing).vertices.map
    (fun vertex => Cell.add (1,1) (Cell.scale 2 (position source drawing vertex)))).Nodup
  simpa only [subdivisionDrawing,List.map_map,Function.comp_def] using mapped

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
