import LeanTrominoes.RetainedAngularFanFinalCarrierLensSingletonGeometry
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFailure

/-!
# Orthogonality of final fallback routes

A failed final direct-source choice is represented by either a carrier lens
or a bend corner.  Both finite component drawings are orthogonal.  This file
transports that property through the physical translation used by final
route occurrences and packages the two fallback cases behind one interface.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every segment of a physical final occurrence represented by bend
metadata remains axis-aligned after translation into the final drawing. -/
theorem
    FinalGaugedRouteOccurrenceWitness.routeSegments_axisAligned_of_bend
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.metadata.source =
        .bend routeBend localClauseIndex)
    (segment : GridSegment)
    (segmentMember :
      segment ∈
        gridPolylineSegments
          (finalGaugedRouteOccurrence
            formula clauseIndex literalIndex (0, 0))) :
    segment.IsAxisAligned := by
  have valid := witness.metadata_retainedValid
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have orthogonal :
      (drawingPlanarSATBendCornerIncidenceDrawing
        formula routeBend).IsOrthogonal :=
    (drawingPlanarSATBendCornerIncidenceDrawing_isValid
      wellFormed degree isLocal valid'.1).2.1
  have clauseMember :
      (witness.metadata.clause, localClauseIndex) ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).formula.zipIdx := by
    rw [drawingPlanarSATBendCornerIncidenceDrawing_formula
      formula routeBend]
    exact valid'.2
  rw [witness.routeEq] at segmentMember
  unfold metadataPhysicalRouteOccurrence translatePolyline
    at segmentMember
  rw [EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add]
    at segmentMember
  rcases List.mem_map.mp segmentMember with
    ⟨physicalSegment, physicalSegmentMember, segmentEq⟩
  subst segment
  apply
    (GridSegment.isAxisAligned_translate _ _).mpr
  apply
    (drawingPlanarSATBendCornerIncidenceDrawing formula routeBend)
      |>.embeddedSegment_isAxisAligned_of_members
        orthogonal clauseMember witness.literalMember
  simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.metadataLookup, sourceEq,
    DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using
      physicalSegmentMember

/-- A final physical route represented by either fallback component family
is an orthogonal polyline. -/
theorem
    FinalGaugedRouteOccurrenceWitness.routeOrthogonal_of_carrier_or_bend
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (sourceCases :
      (∃ link localClauseIndex,
          witness.metadata.source =
            .carrier link localClauseIndex) ∨
        (∃ routeBend localClauseIndex,
          witness.metadata.source =
            .bend routeBend localClauseIndex)) :
    OrthogonalPolyline
      (finalGaugedRouteOccurrence
        formula clauseIndex literalIndex (0, 0)) := by
  rw [orthogonalPolyline_iff_segments]
  intro segment segmentMember
  rcases sourceCases with
      ⟨link, localClauseIndex, sourceEq⟩ |
      ⟨routeBend, localClauseIndex, sourceEq⟩
  · exact
      witness.routeSegments_axisAligned_of_carrier
        wellFormed degree isLocal
        link localClauseIndex sourceEq
        segment segmentMember
  · exact
      witness.routeSegments_axisAligned_of_bend
        wellFormed degree isLocal
        routeBend localClauseIndex sourceEq
        segment segmentMember

end PeriodicOrthocrossing
end LeanTrominoes
