/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- Different active variable/slot entries select different lifted source
route identities.  In fact, the stable route index alone already determines
the incidence metadata and hence the active entry. -/
theorem occurrenceSourceRouteKey_injective
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) :
    Function.Injective (occurrenceSourceRouteKey presentation) := by
  intro first second keyEqual
  let firstData := occurrenceSpliceData presentation first
  let secondData := occurrenceSpliceData presentation second
  have indexEqual :
      firstData.indexed.2 = secondData.indexed.2 := by
    exact congrArg Prod.fst keyEqual
  have firstAt := firstData.indexedMember
  have secondAt := secondData.indexedMember
  rw [List.mem_zipIdx_iff_getElem?] at firstAt secondAt
  have incidenceEqual :
      firstData.indexed.1 = secondData.indexed.1 := by
    rw [indexEqual] at firstAt
    exact Option.some.inj (firstAt.symm.trans secondAt)
  have taggedEqual :
      firstData.tagged = secondData.tagged := by
    calc
      firstData.tagged =
          incidenceTaggedOccurrence firstData.indexed.1 :=
        firstData.metadataEq.symm
      _ = incidenceTaggedOccurrence secondData.indexed.1 :=
        congrArg incidenceTaggedOccurrence incidenceEqual
      _ = secondData.tagged :=
        secondData.metadataEq
  have firstAtom :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase first.1.1 first.1.2 firstData.tagged
      firstData.occurrenceLookup).2
  have secondAtom :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase second.1.1 second.1.2 secondData.tagged
      secondData.occurrenceLookup).2
  have atomEqual : first.1.1 = second.1.1 := by
    calc
      first.1.1 = firstData.tagged.1.atom := firstAtom.symm
      _ = secondData.tagged.1.atom :=
        congrArg (fun tagged => tagged.1.atom) taggedEqual
      _ = second.1.1 := secondAtom
  have firstLookup :
      occurrenceAt source.erase second.1.1 first.1.2 =
        some secondData.tagged := by
    simpa [atomEqual, taggedEqual] using
      firstData.occurrenceLookup
  have slotEqual : first.1.2 = second.1.2 :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_slot_unique
      source.erase second.1.1 secondData.tagged
      first.1.2 second.1.2
      firstLookup secondData.occurrenceLookup
  apply Subtype.ext
  exact Prod.ext atomEqual slotEqual

/-- Unequal active entries have unequal lifted-route keys. -/
theorem occurrenceSourceRouteKey_ne_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second) :
    occurrenceSourceRouteKey presentation first ≠
      occurrenceSourceRouteKey presentation second :=
  fun equal =>
    different
      (occurrenceSourceRouteKey_injective presentation equal)

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

/-- Source routes selected by any two unequal active entries satisfy complete
continuous separation. -/
theorem occurrenceSourceRoutes_avoidEachOther_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second) :
    RoutesAvoidEachOther
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation first)
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation second) :=
  occurrenceSourceRoutes_avoidEachOther presentation first second
    (occurrenceSourceRouteKey_ne_of_ne
      presentation.toPlanarIncidencePresentation different)

/-- Unit subdivisions belonging to unequal active entries can meet only at
both routes' advertised outer endpoints. -/
theorem occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second) :
    RoutesMeetOnlyAtEndpoints
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation first)
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation second) :=
  occurrenceUnitSourceRoutes_meetOnlyAtEndpoints
    presentation first second
    (occurrenceSourceRouteKey_ne_of_ne
      presentation.toPlanarIncidencePresentation different)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
