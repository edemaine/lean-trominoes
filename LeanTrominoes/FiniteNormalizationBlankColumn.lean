/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNormalizationSquareRoutes
import LeanTrominoes.PeriodicThreeDMNormalizationStripRouteBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripVertexBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripReadback

/-! # Finite normalization has a blank horizontal seam -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

theorem stripRasterLocation_horizontal_pos {drawing : PeriodicGridDrawing} {point : Cell}
    (inside : drawing.PositionInFundamentalSquare point) :
    0<(stripRasterLocation drawing.gridSize point).1 := by
  change 0<point.1%(drawing.gridSize:Int)
  rw [Int.emod_eq_of_lt (le_of_lt inside.1) inside.2.1]
  exact inside.1

theorem PlanarPresentation.finalStripVertexAssignment_horizontal_pos
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment} (member : assignment∈presentation.finalStripVertexAssignments) :
    0<assignment.1.1 := by
  obtain ⟨vertex,vertexMember,rfl⟩ := List.mem_map.mp member
  have positionMember : presentation.finalNormalizationPosition vertex∈presentation.finalNormalizedVertexPositions := by
    rw [presentation.finalNormalizedVertexPositions_eq_map]
    exact List.mem_map.mpr ⟨vertex,vertexMember,rfl⟩
  have fundamental := presentation.finalNormalizedPositions_in_fundamental_square _ positionMember
  have positive := stripRasterLocation_horizontal_pos fundamental
  rwa [presentation.finalNormalizedGridDrawing_gridSize] at positive

theorem ContinuousPlanarPresentation.finalStripRouteAssignment_horizontal_pos
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets) (sourceInside : presentation.drawing.RoutePointsInFundamentalSquare)
    {assignment : NormalizedCellAssignment}
    (member : assignment∈presentation.toPlanarPresentation.finalStripRouteAssignments) : 0<assignment.1.1 := by
  let planar := presentation.toPlanarPresentation
  obtain ⟨edge,edgeMember,assignmentMember⟩ := List.mem_flatMap.mp member
  have routeMember : planar.finalNormalizationRoute edge∈planar.finalNormalizedGridDrawing.edgeRoutes := by
    rw [planar.finalNormalizedGridDrawing_edgeRoutes_eq_map]
    exact List.mem_map.mpr ⟨edge,edgeMember,rfl⟩
  obtain ⟨leading,before,current,after,rest,routeEq,rfl⟩ :=
    exists_route_triple_of_mem_stripRouteInteriorAssignments planar.finalNormalizationPeriod edge.color assignmentMember
  have currentMember : current∈planar.finalNormalizationRoute edge := by rw [routeEq];simp
  have inside := presentation.finalNormalizedGridDrawing_routePointsInFundamentalSquare
    wellFormed degree zero sourceInside _ routeMember _ currentMember
  have positive := stripRasterLocation_horizontal_pos inside
  rwa [planar.finalNormalizedGridDrawing_gridSize] at positive

theorem ContinuousPlanarPresentation.finalStripCellAssignment_horizontal_pos
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets) (sourceInside : presentation.drawing.RoutePointsInFundamentalSquare)
    {assignment : NormalizedCellAssignment}
    (member : assignment∈presentation.toPlanarPresentation.finalStripCellAssignments) : 0<assignment.1.1 := by
  rcases List.mem_append.mp member with vertexMember|routeMember
  · exact presentation.toPlanarPresentation.finalStripVertexAssignment_horizontal_pos vertexMember
  · exact presentation.finalStripRouteAssignment_horizontal_pos wellFormed degree zero sourceInside routeMember

theorem ContinuousPlanarPresentation.finalStripCellTypeAt_first_column
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets) (sourceInside : presentation.drawing.RoutePointsInFundamentalSquare) (y : Int) :
    presentation.toPlanarPresentation.finalStripCellTypeAt (0,y)=.blank := by
  have lookupNone : presentation.toPlanarPresentation.finalStripCellAssignments.lookup (0,y)=none := by
    rw [List.lookup_eq_none_iff]
    intro assignment member
    have positive := presentation.finalStripCellAssignment_horizontal_pos wellFormed degree zero sourceInside member
    rw [bne_iff_ne]
    intro equal
    have eq := congrArg Prod.fst equal
    omega
  simp only [PlanarPresentation.finalStripCellTypeAt,lookupNone]
  rfl

theorem ContinuousPlanarPresentation.stripNormalizedOrthogonalDrawing_first_column_blank
    {problem : PeriodicThreeDM} (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets) (sourceInside : presentation.drawing.RoutePointsInFundamentalSquare)
    (y : Fin (presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.verticalPeriodPred+1)) :
    presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.get (0,y)=.blank := by
  rw [presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing_get]
  exact presentation.finalStripCellTypeAt_first_column wellFormed degree zero sourceInside y.val
end LeanTrominoes.PeriodicThreeDM
