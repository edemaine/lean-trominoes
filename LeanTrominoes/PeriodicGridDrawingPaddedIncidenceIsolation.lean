/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPaddedIncidenceRoutes
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingBars
import LeanTrominoes.PeriodicGridDrawingRealLiftedVertices

/-! # Enlarged vertex fans remain isolated in all periodic copies -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

def liftedPaddedIncidenceRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (port : GraphPort Vertex) (cell : Cell) : List Cell :=
  enlargedRectangleTemplate (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)
    (Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation cell))
    (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)

theorem liftedPaddedIncidenceRoute_isRealOpenSimple {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) (cell : Cell) :
    GridPolyline.IsRealOpenSimple (liftedPaddedIncidenceRoute graph drawing port cell) :=
  enlargedRectangleTemplate_isRealOpenSimple _ (crossingBound_positive drawing) _ _ _

theorem liftedPaddedIncidenceRoute_orthogonal {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) (cell : Cell) :
    OrthogonalPolyline (liftedPaddedIncidenceRoute graph drawing port cell) :=
  enlargedRectangleTemplate_orthogonal _ (crossingBound_positive drawing) _ _ _

theorem liftedPaddedIncidenceRoute_eq_translate {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) (cell : Cell) :
    liftedPaddedIncidenceRoute graph drawing port cell =
      translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) cell) (paddedIncidenceRoute graph drawing port) := by
  simp only [liftedPaddedIncidenceRoute,paddedIncidenceRoute,enlargedRectangleTemplate,translatePolyline,List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp [Cell.add,Cell.scale,periodTranslation,paddedGridSize] <;> ring

set_option maxRecDepth 2048 in
theorem liftedPaddedIncidenceRoute_in_cell {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port cell) point) :
    (paddedGridSize drawing.gridSize : ℝ)*cell.1 < point.1 ∧
      point.1 < (paddedGridSize drawing.gridSize : ℝ)*(cell.1+1) ∧
      (paddedGridSize drawing.gridSize : ℝ)*cell.2 < point.2 ∧
      point.2 < (paddedGridSize drawing.gridSize : ℝ)*(cell.2+1) := by
  have vertexBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem (port_vertex_mem compatible.1 member))
  rcases vertexBounds with ⟨xPositive,xBound,yPositive,yBound⟩
  have bounds := enlargedRectangleTemplate_real_bounds _ _ _ _ _ contains
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have radiusNonnegative : (0 : ℝ) ≤ crossingBound drawing.gridSize := by positivity
  have gap : 10*(crossingBound drawing.gridSize : ℝ) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast spacing
  have xLower : (1 : ℝ) ≤ (drawing.vertexPosition graph port.vertex).1 := by exact_mod_cast (by omega : 1 ≤ (drawing.vertexPosition graph port.vertex).1)
  have yLower : (1 : ℝ) ≤ (drawing.vertexPosition graph port.vertex).2 := by exact_mod_cast (by omega : 1 ≤ (drawing.vertexPosition graph port.vertex).2)
  have xUpper : ((drawing.vertexPosition graph port.vertex).1 : ℝ)+1 ≤ drawing.gridSize := by exact_mod_cast (by omega : (drawing.vertexPosition graph port.vertex).1+1 ≤ drawing.gridSize)
  have yUpper : ((drawing.vertexPosition graph port.vertex).2 : ℝ)+1 ≤ drawing.gridSize := by exact_mod_cast (by omega : (drawing.vertexPosition graph port.vertex).2+1 ≤ drawing.gridSize)
  simp only [Cell.add,periodTranslation,Cell.scale] at bounds
  push_cast at bounds
  simp only [paddedGridSize,Nat.cast_mul]
  refine ⟨?_,?_,?_,?_⟩
  all_goals nlinarith [(abs_le.mp bounds.1).1,(abs_le.mp bounds.1).2,(abs_le.mp bounds.2).1,(abs_le.mp bounds.2).2]

theorem liftedPaddedIncidenceRoutes_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first last : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (lastMember : last ∈ allPorts graph)
    (firstCell lastCell : Cell) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing first firstCell) point)
    (lastContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing last lastCell) point) :
    first.vertex = last.vertex ∧ firstCell = lastCell ∧
      (first = last ∨ point = realCell (Cell.scale (paddedRefinementFactor drawing.gridSize)
        (Cell.add (drawing.vertexPosition graph first.vertex) (drawing.periodTranslation firstCell)))) := by
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have positions := enlargedRectangleTemplate_contacts_same_position spacing _ _ _ _ firstContains lastContains
  have occurrences := compatible.lifted_vertex_eq (port_vertex_mem compatible.1 firstMember)
    (port_vertex_mem compatible.1 lastMember) positions
  refine ⟨occurrences.1,occurrences.2,?_⟩
  by_cases same : first = last
  · exact Or.inl same
  apply Or.inr
  have lastValid := incidenceAnchorIndex_valid distinct degree lastMember
  rw [← occurrences.1] at lastValid
  apply enlargedRectangleTemplate_contacts_center _ (crossingBound_positive drawing) _ _ _ _
    (vertexAnchorProfile_degree_le_four distinct degree _) (incidenceAnchorIndex_valid distinct degree firstMember) lastValid
    (fun equal => same (incidenceAnchorIndex_injective degree firstMember lastMember occurrences.1 equal)) firstContains
  simpa only [liftedPaddedIncidenceRoute,← occurrences.1,← occurrences.2] using lastContains

theorem paddedCrossingBar_avoids_incidence_route {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {height : ℚ}
    (crossing : rationalResidue drawing.gridSize height ∈ verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)))
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (cell : Cell) {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains
      (enlargedCrossingBar (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) line
        (paddedPeriodicColumnHeight graph drawing line height)) point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port cell) point) : False :=
  paddedCrossingBar_avoids_lifted_rectangle compatible degree crossing
    (compatible.vertexPosition_mem (port_vertex_mem compatible.1 member)) cell _ _ barContains fanContains

end LeanTrominoes.PeriodicGridDrawing
