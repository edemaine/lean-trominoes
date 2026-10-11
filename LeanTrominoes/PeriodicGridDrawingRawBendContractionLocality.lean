/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendContractionDrawing
import LeanTrominoes.PeriodicGridDrawingRawBendParentPieceLocality
import LeanTrominoes.PeriodicGridDrawingRealLocalBounds

/-! # Joined cubic routes stay in the original neighboring pair of cells -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement

theorem refinedPiece_inside_parent_rectangle {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record ∈ parentRecords drawing parent)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (refinedPiece source drawing record) point) :
    ParentRectangleContains drawing parent.1.offset point := by
  have globalMember := parentRecord_mem parentMember member
  obtain ⟨piece,pieceMember,equal⟩ := List.mem_map.mp member
  have edgeEqual : piece.1=record.2 := congrArg Prod.snd equal
  have chainMember : record.2 ∈ chainEdges (nodes parent (middle drawing parent)) := by
    rw [← edgeEqual]
    exact List.fst_mem_of_mem_zipIdx pieceMember
  exact parent_piece_inside_rectangle planar drawingLocal parentMember (recordIndex_tagged globalMember)
    chainMember contains

theorem contractedDrawing_local {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    (degree : source.DegreeAtMost 4) : (contractedDrawing source drawing).IsRealLocal source := by
  intro parent parentMember p contains
  rw [contractedDrawing_edgeRoute parentMember] at contains
  obtain ⟨route,routeMember,routeContains⟩ := GridPolyline.joinRouteChain_contains
    (parentPieces_chain planar parentMember)
    (fun route member => (parentPieces_openSimple planar degree parentMember member).1) contains
  obtain ⟨record,recordMember,rfl⟩ := List.mem_map.mp routeMember
  have bounds := refinedPiece_inside_parent_rectangle planar localDrawing parentMember recordMember routeContains
  apply real_local_of_rectangle (localGraph parent.1 (List.fst_mem_of_mem_zipIdx parentMember))
  have nonnegative : (0 : Int) ≤ cubicScale drawing := by
    rw [← cubicFactor_cast]
    exact Int.natCast_nonneg _
  have lower (coordinate : Int) :
      cubicScale drawing*min 0 ((drawing.gridSize : Int)*coordinate) =
        min 0 ((cubicScale drawing*(drawing.gridSize : Int))*coordinate) := by
    rw [mul_min_of_nonneg _ _ nonnegative,mul_zero,mul_assoc]
  have upper (coordinate : Int) :
      cubicScale drawing*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*coordinate)) =
        cubicScale drawing*(drawing.gridSize : Int)+max 0 ((cubicScale drawing*(drawing.gridSize : Int))*coordinate) := by
    rw [mul_add,mul_max_of_nonneg _ _ nonnegative,mul_zero,mul_assoc]
  simpa only [ParentRectangleContains,contractedDrawing_gridSize,Nat.cast_mul,cubicFactor_cast,
    ← Int.cast_mul,lower,upper] using bounds

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
