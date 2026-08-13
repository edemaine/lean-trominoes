/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PeriodicGridDrawingRibbonSeparation

/-!
# Separation preserved by orthogonal loop erasure

This module transports complete two-route separation through unit
subdivision and the verified loop-erasure normalizer.  The geometric core is
that every subdivided unit edge is a closed subsegment of one original edge,
so an intersection of retained open edges would already have been an
intersection of original open edges.
-/

namespace LeanTrominoes

set_option maxHeartbeats 2000000

namespace GridSegment

/-- If the endpoints of two intersecting child segments lie on two
axis-aligned parent segments, then the parent interiors also meet. -/
theorem interiorsMeet_of_interiorsMeet_of_endpointsContained
    {firstChild secondChild firstParent secondParent : GridSegment}
    (firstParentAligned : firstParent.IsAxisAligned)
    (secondParentAligned : secondParent.IsAxisAligned)
    (firstStart : firstParent.Contains firstChild.start)
    (firstFinish : firstParent.Contains firstChild.finish)
    (secondStart : secondParent.Contains secondChild.start)
    (secondFinish : secondParent.Contains secondChild.finish)
    (childrenMeet : firstChild.InteriorsMeet secondChild) :
    firstParent.InteriorsMeet secondParent := by
  rcases firstChild with ⟨⟨firstChildStartX, firstChildStartY⟩,
    ⟨firstChildFinishX, firstChildFinishY⟩⟩
  rcases secondChild with ⟨⟨secondChildStartX, secondChildStartY⟩,
    ⟨secondChildFinishX, secondChildFinishY⟩⟩
  rcases firstParent with ⟨⟨firstStartX, firstStartY⟩,
    ⟨firstFinishX, firstFinishY⟩⟩
  rcases secondParent with ⟨⟨secondStartX, secondStartY⟩,
    ⟨secondFinishX, secondFinishY⟩⟩
  simp only [IsAxisAligned, IsHorizontal, IsVertical] at firstParentAligned secondParentAligned
  simp only [Contains, IsHorizontal, IsVertical, Between] at firstStart firstFinish secondStart secondFinish
  simp only [InteriorsMeet, IsHorizontal, IsVertical,
    OpenIntervalsOverlap, StrictlyBetween] at childrenMeet ⊢
  rcases firstParentAligned with firstHorizontal | firstVertical <;>
    rcases secondParentAligned with secondHorizontal | secondVertical <;>
    rcases firstStart with ⟨_, _, firstStartBounds⟩ | ⟨_, _, firstStartBounds⟩ <;>
    rcases firstStartBounds with firstStartBounds | firstStartBounds <;>
    rcases firstFinish with ⟨_, _, firstFinishBounds⟩ | ⟨_, _, firstFinishBounds⟩ <;>
    rcases firstFinishBounds with firstFinishBounds | firstFinishBounds <;>
    rcases secondStart with ⟨_, _, secondStartBounds⟩ | ⟨_, _, secondStartBounds⟩ <;>
    rcases secondStartBounds with secondStartBounds | secondStartBounds <;>
    rcases secondFinish with ⟨_, _, secondFinishBounds⟩ | ⟨_, _, secondFinishBounds⟩ <;>
    rcases secondFinishBounds with secondFinishBounds | secondFinishBounds <;>
    rcases childrenMeet with childHorizontal | childVertical |
      childHorizontalVertical | childVerticalHorizontal <;>
    simp_all [min_def, max_def] <;>
    omega

end GridSegment

namespace AxisDirection

/-- Consecutive geometric segments of a graph walk's support are its
directed darts with the adjacency proofs forgotten. -/
theorem gridPolylineSegments_support_eq_darts_map
    {source target : Cell}
    (walk : unitAxisGraph.Walk source target) :
    gridPolylineSegments walk.support =
      walk.darts.map fun dart =>
        GridSegment.mk dart.fst dart.snd := by
  induction walk with
  | nil => simp [gridPolylineSegments]
  | cons adjacent tail induction =>
      cases tail with
      | nil => simp [gridPolylineSegments]
      | cons next rest =>
          simp [gridPolylineSegments] at induction ⊢
          exact induction

/-- Every normalized directed segment is retained from the ordered unit
subdivision of the source route. -/
theorem normalizeOrthogonalPolyline_segments_sublist_unitSubdividePolyline
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    List.Sublist
      (gridPolylineSegments (normalizeOrthogonalPolyline points))
      (gridPolylineSegments (unitSubdividePolyline points)) := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  unfold eraseOrthogonalLoops
  rw [gridPolylineSegments_support_eq_darts_map]
  have sourceSegments :
      gridPolylineSegments (unitSubdividePolyline points) =
        (orthogonalUnitWalk nonempty orthogonal).darts.map
          (fun dart => GridSegment.mk dart.fst dart.snd) := by
    simpa only [orthogonalUnitWalk,
      SimpleGraph.Walk.support_ofSupport] using
        gridPolylineSegments_support_eq_darts_map
          (orthogonalUnitWalk nonempty orthogonal)
  rw [sourceSegments]
  exact
    (eraseOrthogonalLoops_darts_sublist
      nonempty orthogonal).map
        (fun dart => GridSegment.mk dart.fst dart.snd)

/-- Every generated point of one subdivided source segment lies on that
source segment, including its endpoints. -/
theorem unitSegmentPoints_mem_parent
    {first second point : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned)
    (pointMember : point ∈ unitSegmentPoints first second) :
    (GridSegment.mk first second).Contains point := by
  rcases unitSegmentPoints_mem_endpoint_or_interior
      aligned pointMember with
    pointFirst | pointSecond | interior
  · rw [pointFirst]
    exact GridSegment.contains_start_of_axisAligned aligned
  · rw [pointSecond]
    exact GridSegment.contains_finish_of_axisAligned aligned
  · exact GridSegment.contains_of_interiorContains interior

/-- Every segment of an orthogonal route's unit subdivision is a closed
subsegment of some original route segment. -/
theorem unitSubdividePolyline_segment_provenance
    {points : List Cell}
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points)
    {child : GridSegment}
    (childMember :
      child ∈ gridPolylineSegments (unitSubdividePolyline points)) :
    ∃ parent ∈ gridPolylineSegments points,
      parent.Contains child.start ∧
        parent.Contains child.finish := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [unitSubdividePolyline, gridPolylineSegments] at childMember
  | singleton point =>
      simp [unitSubdividePolyline, gridPolylineSegments] at childMember
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      have firstLast :
          (unitSegmentPoints first second).getLast? = some second :=
        unitSegmentPoints_getLast? parts.1
      have tailHead :
          (unitSubdividePolyline (second :: rest)).head? =
            some second := by
        simpa using unitSubdividePolyline_head?
          (points := second :: rest) (by simp)
      rw [unitSubdividePolyline,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_joinAtEndpoint
          firstLast tailHead,
        List.mem_append] at childMember
      rcases childMember with firstSegmentMember | tailSegmentMember
      · have endpoints :=
          gridPolylineSegments_endpoints_mem firstSegmentMember
        exact
          ⟨GridSegment.mk first second,
            by simp [gridPolylineSegments],
            unitSegmentPoints_mem_parent parts.1 endpoints.1,
            unitSegmentPoints_mem_parent parts.1 endpoints.2⟩
      · rcases tailInduction second parts.2 tailSegmentMember with
          ⟨parent, parentMember, startContained, finishContained⟩
        exact
          ⟨parent,
            by
              simp only [gridPolylineSegments, List.mem_cons]
              exact Or.inr parentMember,
            startContained, finishContained⟩

end AxisDirection

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

open PeriodicOrthocrossing

/-- Unit subdivision and loop erasure advertise exactly the same two outer
endpoints. -/
theorem routePointIsEndpoint_normalizeOrthogonalPolyline_iff_unitSubdividePolyline
    {route : List Cell} {point : Cell}
    (nonempty : route ≠ [])
    (orthogonal : OrthogonalPolyline route) :
    RoutePointIsEndpoint
        (AxisDirection.normalizeOrthogonalPolyline route) point ↔
      RoutePointIsEndpoint
        (AxisDirection.unitSubdividePolyline route) point := by
  unfold RoutePointIsEndpoint
  rw [AxisDirection.normalizeOrthogonalPolyline_head?
      nonempty orthogonal,
    AxisDirection.normalizeOrthogonalPolyline_getLast?
      nonempty orthogonal,
    AxisDirection.unitSubdividePolyline_head? nonempty,
    AxisDirection.unitSubdividePolyline_getLast?
      nonempty orthogonal]

/-- Endpoint-only listed contacts survive pointwise loop erasure. -/
theorem routesMeetOnlyAtEndpoints_normalizeOrthogonalPolyline
    {first second : List Cell}
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (avoids : RoutesAvoidEachOther first second) :
    RoutesMeetOnlyAtEndpoints
      (AxisDirection.normalizeOrthogonalPolyline first)
      (AxisDirection.normalizeOrthogonalPolyline second) := by
  have unitContacts :=
    routesMeetOnlyAtEndpoints_unitSubdividePolyline
      firstNonempty secondNonempty
      firstOrthogonal secondOrthogonal avoids
  intro firstIndex secondIndex pointsEqual
  have firstNormalizedMember :
      (AxisDirection.normalizeOrthogonalPolyline first).get firstIndex ∈
        AxisDirection.normalizeOrthogonalPolyline first :=
    List.get_mem _ firstIndex
  have secondNormalizedMember :
      (AxisDirection.normalizeOrthogonalPolyline second).get secondIndex ∈
        AxisDirection.normalizeOrthogonalPolyline second :=
    List.get_mem _ secondIndex
  have firstUnitMember :
      (AxisDirection.normalizeOrthogonalPolyline first).get firstIndex ∈
        AxisDirection.unitSubdividePolyline first :=
    (AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      firstNonempty firstOrthogonal).subset firstNormalizedMember
  have secondUnitMember :
      (AxisDirection.normalizeOrthogonalPolyline second).get secondIndex ∈
        AxisDirection.unitSubdividePolyline second :=
    (AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      secondNonempty secondOrthogonal).subset secondNormalizedMember
  rcases List.mem_iff_get.mp firstUnitMember with
    ⟨firstUnitIndex, firstUnitEquation⟩
  rcases List.mem_iff_get.mp secondUnitMember with
    ⟨secondUnitIndex, secondUnitEquation⟩
  have contacts :=
    unitContacts firstUnitIndex secondUnitIndex
      (firstUnitEquation.trans
        (pointsEqual.trans secondUnitEquation.symm))
  rw [firstUnitEquation, secondUnitEquation] at contacts
  exact
    ⟨(routePointIsEndpoint_normalizeOrthogonalPolyline_iff_unitSubdividePolyline
        firstNonempty firstOrthogonal).mpr contacts.1,
      (routePointIsEndpoint_normalizeOrthogonalPolyline_iff_unitSubdividePolyline
        secondNonempty secondOrthogonal).mpr contacts.2⟩

/-- Complete continuous two-route separation is preserved by pointwise
unit subdivision and verified loop erasure. -/
theorem RoutesAvoidEachOther.normalizeOrthogonalPolyline
    {first second : List Cell}
    (avoids : RoutesAvoidEachOther first second)
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second) :
    RoutesAvoidEachOther
      (AxisDirection.normalizeOrthogonalPolyline first)
      (AxisDirection.normalizeOrthogonalPolyline second) := by
  unfold RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstChildIndex secondChildIndex childrenMeet
    let firstChild :=
      (gridPolylineSegments
        (AxisDirection.normalizeOrthogonalPolyline first)).get
          firstChildIndex
    let secondChild :=
      (gridPolylineSegments
        (AxisDirection.normalizeOrthogonalPolyline second)).get
          secondChildIndex
    have firstChildMember :
        firstChild ∈
          gridPolylineSegments
            (AxisDirection.normalizeOrthogonalPolyline first) :=
      List.get_mem _ firstChildIndex
    have secondChildMember :
        secondChild ∈
          gridPolylineSegments
            (AxisDirection.normalizeOrthogonalPolyline second) :=
      List.get_mem _ secondChildIndex
    have firstUnitMember :
        firstChild ∈
          gridPolylineSegments
            (AxisDirection.unitSubdividePolyline first) :=
      (AxisDirection.normalizeOrthogonalPolyline_segments_sublist_unitSubdividePolyline
        firstNonempty firstOrthogonal).subset firstChildMember
    have secondUnitMember :
        secondChild ∈
          gridPolylineSegments
            (AxisDirection.unitSubdividePolyline second) :=
      (AxisDirection.normalizeOrthogonalPolyline_segments_sublist_unitSubdividePolyline
        secondNonempty secondOrthogonal).subset secondChildMember
    rcases
        AxisDirection.unitSubdividePolyline_segment_provenance
          firstOrthogonal firstUnitMember with
      ⟨firstParent, firstParentMember,
        firstStartContained, firstFinishContained⟩
    rcases
        AxisDirection.unitSubdividePolyline_segment_provenance
          secondOrthogonal secondUnitMember with
      ⟨secondParent, secondParentMember,
        secondStartContained, secondFinishContained⟩
    have firstParentAligned :=
      (orthogonalPolyline_iff_segments first).mp
        firstOrthogonal firstParent firstParentMember
    have secondParentAligned :=
      (orthogonalPolyline_iff_segments second).mp
        secondOrthogonal secondParent secondParentMember
    have parentInteriorsMeet :=
      GridSegment.interiorsMeet_of_interiorsMeet_of_endpointsContained
        firstParentAligned secondParentAligned
        firstStartContained firstFinishContained
        secondStartContained secondFinishContained childrenMeet
    rcases List.mem_iff_get.mp firstParentMember with
      ⟨firstParentIndex, firstParentEquation⟩
    rcases List.mem_iff_get.mp secondParentMember with
      ⟨secondParentIndex, secondParentEquation⟩
    apply avoids.1 firstParentIndex secondParentIndex
    rw [firstParentEquation, secondParentEquation]
    exact parentInteriorsMeet
  · intro firstPointIndex secondSegmentIndex
    have secondSegmentMember :=
      List.get_mem
        (gridPolylineSegments
          (AxisDirection.normalizeOrthogonalPolyline second))
        secondSegmentIndex
    have secondUnit :=
      (AxisDirection.unitSteps_iff_segments
        (AxisDirection.normalizeOrthogonalPolyline second)).mp
        (AxisDirection.normalizeOrthogonalPolyline_unitSteps
          secondNonempty secondOrthogonal)
        _ secondSegmentMember
    exact secondUnit.not_interiorContains
  · intro secondPointIndex firstSegmentIndex
    have firstSegmentMember :=
      List.get_mem
        (gridPolylineSegments
          (AxisDirection.normalizeOrthogonalPolyline first))
        firstSegmentIndex
    have firstUnit :=
      (AxisDirection.unitSteps_iff_segments
        (AxisDirection.normalizeOrthogonalPolyline first)).mp
        (AxisDirection.normalizeOrthogonalPolyline_unitSteps
          firstNonempty firstOrthogonal)
        _ firstSegmentMember
    exact firstUnit.not_interiorContains
  · exact
      routesMeetOnlyAtEndpoints_normalizeOrthogonalPolyline
        firstNonempty secondNonempty
        firstOrthogonal secondOrthogonal avoids

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

end LeanTrominoes
