/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleChordGeometry

/-! # Chords from distinct original edges form a noninterlacing rectangle matching -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem rectangle_input_noninterlacing {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {a b c d : RectanglePortKey Vertex} (aValid : a.Valid graph drawing column) (bValid : b.Valid graph drawing column)
    (cValid : c.Valid graph drawing column) (dValid : d.Valid graph drawing column)
    (firstParent : a.parentKey = b.parentKey) (secondParent : c.parentKey = d.parentKey)
    (differentParents : a.parentKey ≠ c.parentKey)
    (firstOrder : (a.virtualPort graph drawing column).Before (b.virtualPort graph drawing column))
    (secondOrder : (c.virtualPort graph drawing column).Before (d.virtualPort graph drawing column)) :
    RealRectangleBoundary.Noninterlacing (a.virtualPort graph drawing column) (b.virtualPort graph drawing column)
      (c.virtualPort graph drawing column) (d.virtualPort graph drawing column) := by
  have widthPositive : (0 : ℝ) < ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) := by
    exact_mod_cast virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℝ) < drawing.gridSize := by
    have positive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
    exact_mod_cast positive
  have adParents : a.parentKey ≠ d.parentKey := by rw [← secondParent]; exact differentParents
  have bcParents : b.parentKey ≠ c.parentKey := by rw [← firstParent]; exact differentParents
  have bdParents : b.parentKey ≠ d.parentKey := by rw [← firstParent,← secondParent]; exact differentParents
  have firstSides : (a.virtualPort graph drawing column).side ≠ (b.virtualPort graph drawing column).side := by
    intro same
    have equal := rectanglePort_same_parent_unique_side planar straight column aValid bValid firstParent same
    rw [equal] at firstOrder
    exact lt_irrefl _ firstOrder
  have secondSides : (c.virtualPort graph drawing column).side ≠ (d.virtualPort graph drawing column).side := by
    intro same
    have equal := rectanglePort_same_parent_unique_side planar straight column cValid dValid secondParent same
    rw [equal] at secondOrder
    exact lt_irrefl _ secondOrder
  have aContains := rectanglePort_parent_realInteriorContains planar straight column aValid
  have bContains := rectanglePort_parent_realInteriorContains planar straight column bValid
  have cContains := rectanglePort_parent_realInteriorContains planar straight column cValid
  have dContains := rectanglePort_parent_realInteriorContains planar straight column dValid
  rw [← firstParent] at bContains
  rw [← secondParent] at dContains
  exact RealRectangleBoundary.shifted_noninterlacing_of_disjoint_interiors widthPositive heightPositive
    (rectanglePort_virtual_inside planar graphLocal straight column aValid) (rectanglePort_virtual_inside planar graphLocal straight column bValid)
    (rectanglePort_virtual_inside planar graphLocal straight column cValid) (rectanglePort_virtual_inside planar graphLocal straight column dValid)
    firstOrder secondOrder
    ⟨rectanglePort_ne_of_parent_ne planar straight column aValid cValid differentParents,
      rectanglePort_ne_of_parent_ne planar straight column aValid dValid adParents,
      rectanglePort_ne_of_parent_ne planar straight column bValid cValid bcParents,
      rectanglePort_ne_of_parent_ne planar straight column bValid dValid bdParents⟩ firstSides secondSides
    (GridSegment.realInteriorContains_implies_realContains aContains) (GridSegment.realInteriorContains_implies_realContains bContains)
    (GridSegment.realInteriorContains_implies_realContains cContains) (GridSegment.realInteriorContains_implies_realContains dContains)
    (fun _ => rectanglePort_parent_interiors_disjoint planar straight aValid cValid differentParents)

theorem rectangle_integral_input_noninterlacing {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {a b c d : RectanglePortKey Vertex} (aValid : a.Valid graph drawing column) (bValid : b.Valid graph drawing column)
    (cValid : c.Valid graph drawing column) (dValid : d.Valid graph drawing column)
    (firstParent : a.parentKey = b.parentKey) (secondParent : c.parentKey = d.parentKey)
    (differentParents : a.parentKey ≠ c.parentKey)
    (firstOrder : (a.virtualPort graph drawing column).Before (b.virtualPort graph drawing column))
    (secondOrder : (c.virtualPort graph drawing column).Before (d.virtualPort graph drawing column)) :
    OrthogonalBoundaryRouting.Noninterlacing (a.integralPort graph drawing column,b.integralPort graph drawing column)
      (c.integralPort graph drawing column,d.integralPort graph drawing column) :=
  RectangleBoundaryMatchingTransport.keys_preserve_noninterlacing
    (valid := fun key => key.Valid graph drawing column)
    (oldPort := fun key => key.virtualPort graph drawing column)
    (newPort := fun key => key.integralPort graph drawing column)
    (fun first firstValid second secondValid => rectanglePort_preserves_before planar degree graphLocal straight column
      (first := first) (second := second) firstValid secondValid)
    (a := a) (b := b) (c := c) (d := d)
    aValid bValid cValid dValid
    (rectangle_input_noninterlacing planar graphLocal straight column (a := a) (b := b) (c := c) (d := d) aValid bValid cValid dValid
      firstParent secondParent differentParents firstOrder secondOrder)

end LeanTrominoes.PeriodicGridDrawing
