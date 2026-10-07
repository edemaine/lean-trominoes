/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVirtualHorizontalPorts
import LeanTrominoes.OrthogonalBoundaryPortOrder

/-! # Virtual and integral horizontal ports have the same boundary order -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem shiftedSeamAbscissae_lt_iff {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : Nat × Cell} (firstMember : first ∈ seamCrossingCopies graph drawing 0)
    (secondMember : second ∈ seamCrossingCopies graph drawing 0) :
    shiftedSeamAbscissa graph drawing first < shiftedSeamAbscissa graph drawing second ↔
      (drawing.liftedStraightSegment first.1 first.2).rationalLineAbscissa 0 <
        (drawing.liftedStraightSegment second.1 second.2).rationalLineAbscissa 0 := by
  constructor
  · intro ordered
    by_contra wrong
    rcases lt_or_eq_of_le (le_of_not_gt wrong) with reverse | equal
    · exact lt_asymm ordered (shiftedSeamAbscissae_preserve_order secondMember firstMember reverse)
    · have keys := horizontalCrossingCopies_abscissa_injective planar straight 0
        (List.mem_filter.mp firstMember).1 (List.mem_filter.mp secondMember).1 equal.symm
      subst second
      exact lt_irrefl _ ordered
  · exact shiftedSeamAbscissae_preserve_order firstMember secondMember

def finiteHorizontalSlabPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (key : Nat × Cell) (top : Bool) : OrthogonalBoundaryRouting.Port :=
  ⟨if top then 1 else 3,seamCrossingCoordinate graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)-
    (paddedRefinementFactor drawing.gridSize : Int)*seamAssignedSlab graph drawing key-5*crossingBound drawing.gridSize⟩

theorem virtualHorizontalPort_coordinate_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : Nat × Cell} (firstMember : first ∈ seamCrossingCopies graph drawing 0)
    (secondMember : second ∈ seamCrossingCopies graph drawing 0)
    (sameSlab : seamAssignedSlab graph drawing first = seamAssignedSlab graph drawing second)
    (epsilon : ℚ) (top : Bool)
    (ordered : (virtualHorizontalPort graph drawing epsilon first top).coordinate <
      (virtualHorizontalPort graph drawing epsilon second top).coordinate) :
    (finiteHorizontalSlabPort graph drawing first top).coordinate <
      (finiteHorizontalSlabPort graph drawing second top).coordinate := by
  have realOrder : (shiftedSeamAbscissa graph drawing first : ℝ)-seamAssignedSlab graph drawing first-(epsilon : ℝ) <
      (shiftedSeamAbscissa graph drawing second : ℝ)-seamAssignedSlab graph drawing second-(epsilon : ℝ) := by
    simpa only [virtualHorizontalPort,Rat.cast_sub,Rat.cast_intCast] using ordered
  rw [← sameSlab] at realOrder
  have shiftedOrder : shiftedSeamAbscissa graph drawing first < shiftedSeamAbscissa graph drawing second := by
    have realShiftedOrder : (shiftedSeamAbscissa graph drawing first : ℝ) < (shiftedSeamAbscissa graph drawing second : ℝ) := by linarith
    exact_mod_cast realShiftedOrder
  have oldOrder := (shiftedSeamAbscissae_lt_iff planar straight firstMember secondMember).mp shiftedOrder
  have firstCoordMember : (drawing.liftedStraightSegment first.1 first.2).rationalLineAbscissa 0 ∈ seamCrossingAbscissae graph drawing 0 :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨first,firstMember,rfl⟩)
  have secondCoordMember : (drawing.liftedStraightSegment second.1 second.2).rationalLineAbscissa 0 ∈ seamCrossingAbscissae graph drawing 0 :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨second,secondMember,rfl⟩)
  have newOrder := seamCrossingCoordinates_strictMonoOn planar.1.1 degree 0 firstCoordMember secondCoordMember oldOrder
  dsimp only [finiteHorizontalSlabPort]
  rw [← sameSlab]
  omega

theorem virtualHorizontalPort_before {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : Nat × Cell} (firstMember : first ∈ seamCrossingCopies graph drawing 0)
    (secondMember : second ∈ seamCrossingCopies graph drawing 0)
    (sameSlab : seamAssignedSlab graph drawing first = seamAssignedSlab graph drawing second)
    (epsilon : ℚ) (top : Bool)
    (ordered : (virtualHorizontalPort graph drawing epsilon first top).Before (virtualHorizontalPort graph drawing epsilon second top)) :
    (finiteHorizontalSlabPort graph drawing first top).Before (finiteHorizontalSlabPort graph drawing second top) := by
  cases top
  · have coordinateOrder : (virtualHorizontalPort graph drawing epsilon second false).coordinate <
        (virtualHorizontalPort graph drawing epsilon first false).coordinate := by
      simpa [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
        Prod.Lex.toLex_lt_toLex,virtualHorizontalPort] using ordered
    have mappedOrder := virtualHorizontalPort_coordinate_order planar degree straight secondMember firstMember sameSlab.symm epsilon false coordinateOrder
    simpa [finiteHorizontalSlabPort,OrthogonalBoundaryRouting.Port.Before] using mappedOrder
  · have coordinateOrder : (virtualHorizontalPort graph drawing epsilon first true).coordinate <
        (virtualHorizontalPort graph drawing epsilon second true).coordinate := by
      simpa [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
        Prod.Lex.toLex_lt_toLex,virtualHorizontalPort] using ordered
    have mappedOrder := virtualHorizontalPort_coordinate_order planar degree straight firstMember secondMember sameSlab epsilon true coordinateOrder
    simpa [finiteHorizontalSlabPort,OrthogonalBoundaryRouting.Port.Before] using mappedOrder

end LeanTrominoes.PeriodicGridDrawing
