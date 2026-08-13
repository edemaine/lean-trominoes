/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureSeparation
import LeanTrominoes.OrthogonalPolylineStrictSeparation

/-!
# Strict separation under polyline refinement

A refined polyline lists extra points along the segments of a coarser
polyline and splits each coarse segment into smaller collinear segments.
Because this changes neither continuous support nor introduces points away
from that support, contact-free separation from another orthogonal route is
preserved.

The interface here records only the two provenance facts needed by the
separation proof.  Unit subdivision is the first concrete refinement
instance; later geometric constructions can transport the same certificate
through scaling and translation.
-/

namespace LeanTrominoes

/-- Every point and segment of `refined` lies on the polyline represented by
`source`.  Points may be old listed points or lie in a source segment's
relative interior; every refined segment is contained in one source
segment. -/
def PolylineRefines (refined source : List Cell) : Prop :=
  (∀ point ∈ refined,
      point ∈ source ∨
        ∃ segment ∈ gridPolylineSegments source,
          segment.InteriorContains point) ∧
    ∀ child ∈ gridPolylineSegments refined,
      ∃ parent ∈ gridPolylineSegments source,
        parent.Contains child.start ∧
          parent.Contains child.finish

/-- Positive uniform scaling transports a polyline-refinement
certificate. -/
theorem PolylineRefines.scalePolyline
    {refined source : List Cell}
    {factor : Int} (factorPositive : 0 < factor)
    (refines : PolylineRefines refined source) :
    PolylineRefines
      (LeanTrominoes.scalePolyline factor refined)
      (LeanTrominoes.scalePolyline factor source) := by
  constructor
  · intro scaledPoint scaledPointMember
    rcases List.mem_map.mp scaledPointMember with
      ⟨point, pointMember, rfl⟩
    rcases refines.1 point pointMember with
      sourcePoint | ⟨segment, segmentMember, interior⟩
    · exact Or.inl (List.mem_map.mpr
        ⟨point, sourcePoint, rfl⟩)
    · refine Or.inr ⟨segment.scale factor, ?_, ?_⟩
      · rw [gridPolylineSegments_scalePolyline]
        exact List.mem_map.mpr
          ⟨segment, segmentMember, rfl⟩
      · exact
          (GridSegment.interiorContains_scale_iff
            factorPositive segment point).mpr interior
  · intro scaledChild scaledChildMember
    rw [gridPolylineSegments_scalePolyline] at scaledChildMember
    rcases List.mem_map.mp scaledChildMember with
      ⟨child, childMember, rfl⟩
    rcases refines.2 child childMember with
      ⟨parent, parentMember, startContained, finishContained⟩
    refine ⟨parent.scale factor, ?_, ?_, ?_⟩
    · rw [gridPolylineSegments_scalePolyline]
      exact List.mem_map.mpr
        ⟨parent, parentMember, rfl⟩
    · exact
        (GridSegment.contains_scale_iff
          factorPositive parent child.start).mpr startContained
    · exact
        (GridSegment.contains_scale_iff
          factorPositive parent child.finish).mpr finishContained

/-- Common pointwise translation transports a polyline-refinement
certificate. -/
theorem PolylineRefines.translatePolyline
    {refined source : List Cell}
    (refines : PolylineRefines refined source)
    (offset : Cell) :
    PolylineRefines
      (PeriodicOrthocrossing.translatePolyline offset refined)
      (PeriodicOrthocrossing.translatePolyline offset source) := by
  constructor
  · intro translatedPoint translatedPointMember
    rcases List.mem_map.mp translatedPointMember with
      ⟨point, pointMember, rfl⟩
    rcases refines.1 point pointMember with
      sourcePoint | ⟨segment, segmentMember, interior⟩
    · exact Or.inl (List.mem_map.mpr
        ⟨point, sourcePoint, rfl⟩)
    · refine Or.inr ⟨segment.translate offset, ?_, ?_⟩
      · rw [gridPolylineSegments_translatePolyline]
        exact List.mem_map.mpr
          ⟨segment, segmentMember, rfl⟩
      · simpa [Cell.add, add_comm] using
          (PeriodicGridDrawing.interiorContains_translate_iff
            segment offset point).mpr interior
  · intro translatedChild translatedChildMember
    rw [gridPolylineSegments_translatePolyline] at translatedChildMember
    rcases List.mem_map.mp translatedChildMember with
      ⟨child, childMember, rfl⟩
    rcases refines.2 child childMember with
      ⟨parent, parentMember, startContained, finishContained⟩
    refine ⟨parent.translate offset, ?_, ?_, ?_⟩
    · rw [gridPolylineSegments_translatePolyline]
      exact List.mem_map.mpr
        ⟨parent, parentMember, rfl⟩
    · simpa [GridSegment.translate, Cell.add, add_comm] using
        (PeriodicGridDrawing.contains_translate_iff
          parent offset child.start).mpr startContained
    · simpa [GridSegment.translate, Cell.add, add_comm] using
        (PeriodicGridDrawing.contains_translate_iff
          parent offset child.finish).mpr finishContained

/-- Closed betweenness is transitive through a nested interval. -/
private theorem GridSegment.Between.of_nested
    {outerFirst outerLast innerFirst innerLast point : Int}
    (innerFirstBetween :
      GridSegment.Between outerFirst outerLast innerFirst)
    (innerLastBetween :
      GridSegment.Between outerFirst outerLast innerLast)
    (pointBetween :
      GridSegment.Between innerFirst innerLast point) :
    GridSegment.Between outerFirst outerLast point := by
  unfold GridSegment.Between at *
  rcases innerFirstBetween with forwardFirst | backwardFirst <;>
    rcases innerLastBetween with forwardLast | backwardLast <;>
    rcases pointBetween with forwardPoint | backwardPoint
  all_goals omega

/-- A point on a child segment whose endpoints lie on one axis-aligned
parent segment also lies on that parent segment. -/
private theorem GridSegment.contains_of_child
    {parent child : GridSegment} {point : Cell}
    (parentAligned : parent.IsAxisAligned)
    (startContained : parent.Contains child.start)
    (finishContained : parent.Contains child.finish)
    (pointContained : child.Contains point) :
    parent.Contains point := by
  rcases parentAligned with parentHorizontal | parentVertical
  · have startData :
        child.start.2 = parent.start.2 ∧
          GridSegment.Between
            parent.start.1 parent.finish.1 child.start.1 := by
      rcases startContained with horizontal | vertical
      · exact horizontal.2
      · exact (parentHorizontal.2 vertical.1.1).elim
    have finishData :
        child.finish.2 = parent.start.2 ∧
          GridSegment.Between
            parent.start.1 parent.finish.1 child.finish.1 := by
      rcases finishContained with horizontal | vertical
      · exact horizontal.2
      · exact (parentHorizontal.2 vertical.1.1).elim
    rcases pointContained with childHorizontal | childVertical
    · refine Or.inl ⟨parentHorizontal, ?_, ?_⟩
      · exact childHorizontal.2.1.trans startData.1
      · exact GridSegment.Between.of_nested
          startData.2 finishData.2 childHorizontal.2.2
    · exact
        (childVertical.1.2
          (startData.1.trans finishData.1.symm)).elim
  · have startData :
        child.start.1 = parent.start.1 ∧
          GridSegment.Between
            parent.start.2 parent.finish.2 child.start.2 := by
      rcases startContained with horizontal | vertical
      · exact (parentVertical.2 horizontal.1.1).elim
      · exact vertical.2
    have finishData :
        child.finish.1 = parent.start.1 ∧
          GridSegment.Between
            parent.start.2 parent.finish.2 child.finish.2 := by
      rcases finishContained with horizontal | vertical
      · exact (parentVertical.2 horizontal.1.1).elim
      · exact vertical.2
    rcases pointContained with childHorizontal | childVertical
    · exact
        (childHorizontal.1.2
          (startData.1.trans finishData.1.symm)).elim
    · refine Or.inr ⟨parentVertical, ?_, ?_⟩
      · exact childVertical.2.1.trans startData.1
      · exact GridSegment.Between.of_nested
          startData.2 finishData.2 childVertical.2.2

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Refining the first route preserves contact-free separation from an
orthogonal second route. -/
theorem RoutesStrictlyAvoidEachOther.refine_left
    {source refined second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther source second)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline source)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (refines : PolylineRefines refined source) :
    RoutesStrictlyAvoidEachOther refined second := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro child childMember secondSegment secondMember childrenMeet
    rcases refines.2 child childMember with
      ⟨parent, parentMember, childStart, childFinish⟩
    have parentAligned :=
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments source).mp
        sourceOrthogonal parent parentMember
    have secondAligned :=
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments second).mp
        secondOrthogonal secondSegment secondMember
    apply strict.1 parent parentMember secondSegment secondMember
    exact
      GridSegment.interiorsMeet_of_interiorsMeet_of_endpointsContained
        parentAligned secondAligned childStart childFinish
        (GridSegment.contains_start_of_axisAligned secondAligned)
        (GridSegment.contains_finish_of_axisAligned secondAligned)
        childrenMeet
  · intro refinedPoint refinedPointMember
      secondSegment secondMember secondInterior
    rcases refines.1 refinedPoint refinedPointMember with
      sourcePoint | ⟨parent, parentMember, parentInterior⟩
    · exact strict.2.1 refinedPoint sourcePoint
        secondSegment secondMember secondInterior
    · exact strict.1 parent parentMember secondSegment secondMember
        (GridSegment.interiorsMeet_of_interiorContains
          parentInterior secondInterior)
  · intro secondPoint secondPointMember child childMember childInterior
    rcases refines.2 child childMember with
      ⟨parent, parentMember, childStart, childFinish⟩
    have parentAligned :=
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments source).mp
        sourceOrthogonal parent parentMember
    have parentContains : parent.Contains secondPoint :=
      GridSegment.contains_of_child parentAligned
        childStart childFinish
        (GridSegment.contains_of_interiorContains childInterior)
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          parentContains with
      parentInterior | atEndpoint
    · exact strict.2.2.1 secondPoint secondPointMember
        parent parentMember parentInterior
    · have endpoints := gridPolylineSegments_endpoints_mem parentMember
      rcases atEndpoint with atStart | atFinish
      · subst secondPoint
        exact strict.2.2.2 parent.start endpoints.1
          parent.start secondPointMember rfl
      · subst secondPoint
        exact strict.2.2.2 parent.finish endpoints.2
          parent.finish secondPointMember rfl
  · intro refinedPoint refinedPointMember
      secondPoint secondPointMember pointsEqual
    rcases refines.1 refinedPoint refinedPointMember with
      sourcePoint | ⟨parent, parentMember, parentInterior⟩
    · exact strict.2.2.2 refinedPoint sourcePoint
        secondPoint secondPointMember pointsEqual
    · subst secondPoint
      exact strict.2.2.1 refinedPoint secondPointMember
        parent parentMember parentInterior

/-- Refining the second route preserves contact-free separation from an
orthogonal first route. -/
theorem RoutesStrictlyAvoidEachOther.refine_right
    {first source refined : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first source)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline source)
    (refines : PolylineRefines refined source) :
    RoutesStrictlyAvoidEachOther first refined :=
  (strict.symm.refine_left sourceOrthogonal firstOrthogonal refines).symm

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace AxisDirection

/-- Ordered unit subdivision refines the original orthogonal polyline. -/
theorem unitSubdividePolyline_refines
    {source : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline source) :
    PolylineRefines (unitSubdividePolyline source) source := by
  constructor
  · intro point pointMember
    exact
      unitSubdividePolyline_mem_original_or_segmentInterior
        orthogonal pointMember
  · intro child childMember
    exact unitSubdividePolyline_segment_provenance
      orthogonal childMember

end AxisDirection
end LeanTrominoes
