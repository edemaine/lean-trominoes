/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVerticalCoreRouteGeometry
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalVerticalCoreFanContacts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEndpointFanSeparation
import LeanTrominoes.Common.Geometry.GridPolylineRouteWord

/-! # Vertical replacement routes are simple orthogonal chains of two fans and a core -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem verticalFanRouteWord_separated {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    GridPolyline.SeparatedWord (verticalFanRouteWord graph drawing tagged) := by
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have sourceMember := sourcePort_mem_allPorts graph member
  have targetMember := targetPort_mem_allPorts graph member
  have oldX : (drawing.straightSegment tagged.2).start.1 = (drawing.straightSegment tagged.2).finish.1 := by
    simpa [liftedStraightSegment,GridSegment.translate,Cell.add] using vertical
  have nondegenerate := straightSegment_nondegenerate planar.1 member (straight _ member)
  have oldVertical : (drawing.straightSegment tagged.2).IsVertical :=
    ⟨oldX,fun same => nondegenerate (Prod.ext oldX same)⟩
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have ends := planar.1.1.2.2.2.2.2 tagged member
  have sourceEq : (drawing.straightSegment tagged.2).start = drawing.vertexPosition graph tagged.1.source := by
    simp only [straightSegment,ends.1,Option.getD_some]
  have targetEq : (drawing.straightSegment tagged.2).finish = Cell.add
      (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) := by
    simp only [straightSegment,ends.2,Option.getD_some]
  have coreImage : ∀ point, GridPolyline.RealContains (verticalCoreRoute graph drawing tagged) point →
      ((drawing.straightSegment tagged.2).verticalCore (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)).RealContains point := by
    intro point contains
    rw [verticalCoreRoute_eq_segment planar degree straight member vertical] at contains
    simpa [GridPolyline.RealContains,gridPolylineSegments] using contains
  change (_ ∧ _ ∧ (_ ∧ _ ∧ True))
  refine ⟨?_,?_,?_,?_,trivial⟩
  · intro point sourceContains coreContains
    have contact := verticalCore_fan_contact_last oldVertical (crossingBound_positive drawing) spacing
      (coreImage point coreContains) false (vertexAnchorProfile graph drawing tagged.1.source)
      (incidenceAnchorIndex graph drawing (sourcePort tagged.1 tagged.2))
      (vertexAnchorProfile_degree_le_four distinct degree _) (incidenceAnchorIndex_valid distinct degree sourceMember)
      (by simpa only [Bool.false_eq_true,if_false,sourceEq,paddedIncidenceRoute,sourcePort] using sourceContains)
    simpa only [Bool.false_eq_true,if_false,sourceEq,paddedIncidenceRoute,sourcePort] using contact
  · intro later laterMember point sourceContains targetContains
    simp only [List.mem_cons,List.not_mem_nil,or_false] at laterMember
    subst later
    exact endpoint_fans_disjoint planar degree straight member sourceContains
      ((GridPolyline.realContains_reverse _ _).mp targetContains)
  · intro point coreContains targetContains
    have contact := verticalCore_fan_contact_last oldVertical (crossingBound_positive drawing) spacing
      (coreImage point coreContains) true (vertexAnchorProfile graph drawing tagged.1.target)
      (incidenceAnchorIndex graph drawing (targetPort tagged.1 tagged.2))
      (vertexAnchorProfile_degree_le_four distinct degree _) (incidenceAnchorIndex_valid distinct degree targetMember)
      (by simpa only [if_true,targetEq,liftedPaddedIncidenceRoute,targetPort] using
        (GridPolyline.realContains_reverse _ _).mp targetContains)
    simpa only [if_true,targetEq,verticalCoreRoute,List.getLast?_cons_cons,List.getLast?_singleton,
      Option.getD_some,liftedPaddedIncidenceRoute,targetPort] using contact
  · intro later laterMember
    exact (List.not_mem_nil laterMember).elim

theorem verticalFanEdgeRoute_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    GridPolyline.IsRealOpenSimple (verticalFanEdgeRoute graph drawing tagged) ∧
      OrthogonalPolyline (verticalFanEdgeRoute graph drawing tagged) ∧
      ∀ point, GridPolyline.RealContains (verticalFanEdgeRoute graph drawing tagged) point ↔
        ∃ piece ∈ verticalFanRouteWord graph drawing tagged, GridPolyline.RealContains piece point := by
  have core := verticalCoreRoute_valid planar degree straight member vertical
  have simple : ∀ piece ∈ verticalFanRouteWord graph drawing tagged, GridPolyline.IsRealOpenSimple piece := by
    intro piece pieceMember
    simp only [verticalFanRouteWord,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    rcases pieceMember with rfl | rfl | rfl
    · exact paddedIncidenceRoute_isRealOpenSimple graph drawing _
    · exact core.1
    · exact (liftedPaddedIncidenceRoute_isRealOpenSimple graph drawing _ _).reverse
  have orthogonal : ∀ piece ∈ verticalFanRouteWord graph drawing tagged, OrthogonalPolyline piece := by
    intro piece pieceMember
    simp only [verticalFanRouteWord,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    rcases pieceMember with rfl | rfl | rfl
    · exact paddedIncidenceRoute_orthogonal graph drawing _
    · exact core.2.1
    · exact (liftedPaddedIncidenceRoute_orthogonal graph drawing _ _).reverse
  have valid := GridPolyline.joinWord_valid simple orthogonal (verticalFanRouteWord_connected graph drawing tagged)
    (verticalFanRouteWord_separated planar degree straight member vertical)
  exact ⟨valid.1,valid.2.1,valid.2.2.2.2⟩

end LeanTrominoes.PeriodicGridDrawing
