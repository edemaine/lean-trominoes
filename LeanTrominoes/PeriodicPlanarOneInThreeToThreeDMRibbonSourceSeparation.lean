import LeanTrominoes.OrthogonalPolylineRouteReversalContacts
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PeriodicGridDrawingRibbonSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes

/-!
# Separation of exact-one source routes

The source drawing certifies stored clause-to-variable routes in its
periodic lift, while the 3DM construction reverses and rebases those routes.
This file identifies each rebased occurrence by its stored route index and
semantic lattice translate, then transfers complete continuous separation
to the selected variable-to-clause routes and their unit subdivisions.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PositionedPeriodicCNF

/-- A tagged metadata route occurs at the same numeric index in the
incidence drawing's flat route enumeration. -/
theorem PlanarIncidencePresentation.route_zipIdx_mem_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex,
      tagged.2) ∈
      (incidenceDrawing source placement
        presentation.routes).edgeRoutes.zipIdx := by
  change
    (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex,
      tagged.2) ∈
      (incidenceEdgeRoutes source presentation.routes).zipIdx
  rw [incidenceEdgeRoutes_eq_metadata_map, List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨tagged, taggedMember, by cases tagged; rfl⟩

/-- Every tagged source route contains at least two listed points. -/
theorem PlanarIncidencePresentation.route_length_ge_two_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    2 ≤
      (presentation.routes
        tagged.1.clauseIndex tagged.1.literalIndex).length := by
  have segmentsNonempty :=
    presentation.route_segments_ne_nil_of_tagged taggedMember
  have segmentsPositive :
      0 <
        (gridPolylineSegments
          (presentation.routes
            tagged.1.clauseIndex
            tagged.1.literalIndex)).length :=
    List.length_pos_iff.mpr segmentsNonempty
  rw [gridPolylineSegments_length] at segmentsPositive
  omega

/-- The semantic lattice translate used to rebase a stored
clause-to-variable route into its variable-to-clause orientation. -/
def variableToClauseTranslate
    {Variable : Type*}
    (incidence : CNFIncidence Variable) : Cell :=
  Cell.sub
    (PeriodicCNF.clauseAnchor incidence.clause)
    incidence.literal.offset

/-- Distinct lifted stored-route occurrences remain completely separated
after both are reversed and rebased into variable-to-clause routes. -/
theorem PlanarIncidencePresentation.variableToClauseRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    (continuous :
      (incidenceDrawing source placement
        presentation.routes).IsContinuouslyPlanar)
    (endpointContacts :
      (incidenceDrawing source placement presentation.routes)
        |>.RoutePointsMeetOnlyAtEndpoints)
    {first second : CNFIncidence Variable × Nat}
    (firstMember :
      first ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (secondMember :
      second ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (occurrencesDifferent :
      (first.2, variableToClauseTranslate first.1) ≠
        (second.2, variableToClauseTranslate second.1)) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (presentation.variableToClauseRoute first.1)
      (presentation.variableToClauseRoute second.1) := by
  let drawing :=
    incidenceDrawing source placement presentation.routes
  have originalAvoid :=
    PeriodicGridDrawing.routeOccurrences_avoidEachOther
      (drawing := drawing)
      continuous endpointContacts
      (presentation.route_zipIdx_mem_of_tagged firstMember)
      (presentation.route_zipIdx_mem_of_tagged secondMember)
      (presentation.route_length_ge_two_of_tagged firstMember)
      (presentation.route_length_ge_two_of_tagged secondMember)
      (presentation.route_orthogonal_of_tagged firstMember)
      (presentation.route_orthogonal_of_tagged secondMember)
      (variableToClauseTranslate first.1)
      (variableToClauseTranslate second.1)
      occurrencesDifferent
  have reversed :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_reverse
      originalAvoid
  have periodTranslationEq (offset : Cell) :
      drawing.periodTranslation offset =
        placement.translation offset := by
    unfold drawing PeriodicGridDrawing.periodTranslation
      PeriodicVariablePlacement.translation
    rw [incidenceDrawing_gridSize
      source placement presentation.routes
      presentation.periodPositive]
  simpa [PlanarIncidencePresentation.variableToClauseRoute,
    variableToClauseTranslate, translatePolyline,
    List.map_reverse, periodTranslationEq] using reversed

end PositionedPeriodicCNF

namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Identity of the lifted stored route selected for an active occurrence:
its stable route index together with the semantic translate used for
variable-to-clause rebasing. -/
noncomputable def occurrenceSourceRouteKey
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) : Nat × Cell :=
  let data := occurrenceSpliceData presentation entry
  (data.indexed.2,
    PositionedPeriodicCNF.variableToClauseTranslate
      data.indexed.1)

/-- Active occurrence source routes with distinct lifted-route identities
satisfy the complete finite separation predicate. -/
theorem occurrenceSourceRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (different :
      occurrenceSourceRouteKey
          presentation.toPlanarIncidencePresentation first ≠
        occurrenceSourceRouteKey
          presentation.toPlanarIncidencePresentation second) :
    RoutesAvoidEachOther
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation first)
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation second) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  exact
    planar.variableToClauseRoutes_avoidEachOther
      presentation.continuouslyPlanar presentation.endpointContacts
      firstData.indexedMember secondData.indexedMember
      (by
        simpa [occurrenceSourceRouteKey, planar,
          firstData, secondData] using different)

/-- Unit subdivision of two distinct lifted source routes can introduce no
new contact except at the outer endpoints of both subdivided routes. -/
theorem occurrenceUnitSourceRoutes_meetOnlyAtEndpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (different :
      occurrenceSourceRouteKey
          presentation.toPlanarIncidencePresentation first ≠
        occurrenceSourceRouteKey
          presentation.toPlanarIncidencePresentation second) :
    RoutesMeetOnlyAtEndpoints
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation first)
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation second) := by
  apply routesMeetOnlyAtEndpoints_unitSubdividePolyline
  · exact
      List.ne_nil_of_length_pos
        (lt_of_lt_of_le (by decide)
          (occurrenceSourceRoute_length
            presentation.toPlanarIncidencePresentation first))
  · exact
      List.ne_nil_of_length_pos
        (lt_of_lt_of_le (by decide)
          (occurrenceSourceRoute_length
            presentation.toPlanarIncidencePresentation second))
  · exact
      occurrenceSourceRoute_orthogonal
        presentation.toPlanarIncidencePresentation first
  · exact
      occurrenceSourceRoute_orthogonal
        presentation.toPlanarIncidencePresentation second
  · exact
      occurrenceSourceRoutes_avoidEachOther
        presentation first second different

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
