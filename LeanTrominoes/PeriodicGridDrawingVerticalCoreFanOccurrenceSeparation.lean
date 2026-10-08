/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalFanContactVertices
import LeanTrominoes.PeriodicGridDrawingVerticalFanRouteSimple
import LeanTrominoes.GridPolylineRealEndpointContainment

/-! # A vertical core can meet only its own two endpoint fans -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

private theorem contains_lastD {route : List Cell} (long : 2 ≤ route.length) :
    GridPolyline.RealContains route (realCell (route.getLast?.getD (0,0))) := by
  cases last : route.getLast? with
  | none => have empty := List.getLast?_eq_none_iff.mp last; simp [empty] at long
  | some point => simpa only [last,Option.getD_some] using GridPolyline.realContains_last long last

theorem verticalCoreRoute_fan_contact_identifies_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell)
    {point : ℝ × ℝ}
    (coreContains : GridPolyline.RealContains (verticalCoreRoute graph drawing tagged) point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    (port = sourcePort tagged.1 tagged.2 ∧ fanCell = (0,0)) ∨
      (port = targetPort tagged.1 tagged.2 ∧ fanCell = tagged.1.offset) := by
  have oldX : (drawing.straightSegment tagged.2).start.1 = (drawing.straightSegment tagged.2).finish.1 := by
    simpa [liftedStraightSegment,GridSegment.translate,Cell.add] using vertical
  have nondegenerate := straightSegment_nondegenerate planar.1 member (straight _ member)
  have oldVertical : (drawing.straightSegment tagged.2).IsVertical :=
    ⟨oldX,fun same => nondegenerate (Prod.ext oldX same)⟩
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have coreEq := verticalCoreRoute_eq_segment planar degree straight member vertical
  have coreRaw : ((drawing.straightSegment tagged.2).verticalCore (paddedRefinementFactor drawing.gridSize)
      (crossingBound drawing.gridSize)).RealContains point := by
    rw [coreEq] at coreContains
    simpa [GridPolyline.RealContains,gridPolylineSegments] using coreContains
  change [_ , _] = [_ , _] at coreEq
  have firstAnchor := (List.cons.inj coreEq).1
  have lastAnchor := (List.cons.inj (List.cons.inj coreEq).2).1
  have parentContains := GridSegment.verticalCore_realContains_parent oldVertical spacing coreRaw
  have liftedContains : ((drawing.liftedStraightSegment tagged.2 (0,0)).scale (paddedRefinementFactor drawing.gridSize)).RealContains point := by
    simpa [liftedStraightSegment,GridSegment.translate,Cell.add,periodTranslation,Cell.scale] using parentContains
  have vertexContact := scaled_vertical_segment_fan_contact_vertex planar.1 member (straight _ member) (0,0) vertical
    portMember fanCell liftedContains fanContains
  have ends := planar.1.1.2.2.2.2.2 tagged member
  have sourceEq : (drawing.straightSegment tagged.2).start = drawing.vertexPosition graph tagged.1.source := by
    simp only [straightSegment,ends.1,Option.getD_some]
  have targetEq : (drawing.straightSegment tagged.2).finish = Cell.add
      (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) := by
    simp only [straightSegment,ends.2,Option.getD_some]
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  rcases vertexContact with source | target
  · have positionEq : Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell) =
        (drawing.straightSegment tagged.2).start := by
      simpa [liftedStraightSegment,GridSegment.translate,Cell.add,periodTranslation,Cell.scale] using source
    have endpointContact := verticalCore_fan_contact_core_endpoint oldVertical spacing coreRaw false
      (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)
      (by simpa only [Bool.false_eq_true,if_false,← positionEq,liftedPaddedIncidenceRoute] using fanContains)
    rw [← firstAnchor] at endpointContact
    simp only [Bool.false_eq_true,if_false] at endpointContact
    have ownContains := contains_lastD (paddedIncidenceRoute_isRealOpenSimple graph drawing (sourcePort tagged.1 tagged.2)).1
    rw [← endpointContact] at ownContains
    have ownRaw : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2) (0,0)) point := by
      rw [liftedPaddedIncidenceRoute_eq_translate]
      simpa [Cell.scale,translatePolyline_zero] using ownContains
    have contact := liftedPaddedIncidenceRoutes_contact planar.1.1 distinct degree
      (sourcePort_mem_allPorts graph member) portMember (0,0) fanCell ownRaw fanContains
    have portEq : sourcePort tagged.1 tagged.2 = port := by
      rcases contact.2.2 with equal | center
      · exact equal
      · have centerEq : point = realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.straightSegment tagged.2).start) := by
          simpa [sourcePort,← sourceEq,Cell.add,periodTranslation,Cell.scale] using center
        rw [centerEq] at coreRaw
        exact (GridSegment.verticalCore_avoids_scaled_endpoint oldVertical (crossingBound_positive drawing) spacing false coreRaw).elim
    exact Or.inl ⟨portEq.symm,contact.2.1.symm⟩
  · have positionEq : Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell) =
        (drawing.straightSegment tagged.2).finish := by
      simpa [liftedStraightSegment,GridSegment.translate,Cell.add,periodTranslation,Cell.scale] using target
    have endpointContact := verticalCore_fan_contact_core_endpoint oldVertical spacing coreRaw true
      (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)
      (by simpa only [if_true,← positionEq,liftedPaddedIncidenceRoute] using fanContains)
    rw [← lastAnchor] at endpointContact
    simp only [if_true] at endpointContact
    have ownContains := contains_lastD (liftedPaddedIncidenceRoute_isRealOpenSimple graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).1
    rw [← endpointContact] at ownContains
    have contact := liftedPaddedIncidenceRoutes_contact planar.1.1 distinct degree
      (targetPort_mem_allPorts graph member) portMember tagged.1.offset fanCell ownContains fanContains
    have portEq : targetPort tagged.1 tagged.2 = port := by
      rcases contact.2.2 with equal | center
      · exact equal
      · have centerEq : point = realCell (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.straightSegment tagged.2).finish) := by
          simpa only [targetPort,← targetEq] using center
        rw [centerEq] at coreRaw
        exact (GridSegment.verticalCore_avoids_scaled_endpoint oldVertical (crossingBound_positive drawing) spacing true coreRaw).elim
    exact Or.inr ⟨portEq.symm,contact.2.1.symm⟩

end LeanTrominoes.PeriodicGridDrawing
