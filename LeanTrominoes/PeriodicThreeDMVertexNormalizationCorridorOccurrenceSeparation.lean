/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationTemplateOccurrenceSeparation
import LeanTrominoes.PeriodicThreeDMVertexNormalizationCorridorSeparation
import LeanTrominoes.PeriodicGridDrawingUnitSubdivisionRibbon

/-!
# Lifted first-round normalization corridors

This module identifies the three pieces of every lifted first-round route
and proves strict separation of the two trimmed middle corridors belonging
to distinct contracted route occurrences.  The proof transports contracted
route avoidance through scale twelve, common translation, and ordered unit
subdivision; the symmetric endpoint trim then removes every permitted old
endpoint contact.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Trimmed magnified middle belonging to one contracted route occurrence. -/
def PlanarPresentation.firstNormalizationCorridorOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) : List Cell :=
  trimmedMagnifiedRoute
    (presentation.contractedEdgeRouteOccurrence edge routeTranslate)

/-- Exact old-scale endpoints of a lifted contracted route occurrence,
expressed using endpoint-occurrence positions. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_normalizationEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    (presentation.contractedEdgeRouteOccurrence edge routeTranslate).head? =
        some (presentation.contractedEndpointOccurrencePosition
          (.source edge) routeTranslate) ∧
      (presentation.contractedEdgeRouteOccurrence edge routeTranslate).getLast? =
        some (presentation.contractedEndpointOccurrencePosition
          (.target edge) routeTranslate) := by
  have endpoints :=
    presentation.contractedEdgeRoute_normalizationEndpoints edgeMember
  constructor
  · unfold PlanarPresentation.contractedEdgeRouteOccurrence
      PeriodicOrthocrossing.translatePolyline
    simp only [List.head?_map, endpoints.1, Option.map_some]
    rw [presentation.contractedEndpointOccurrencePosition_source]
    rfl
  · unfold PlanarPresentation.contractedEdgeRouteOccurrence
      PeriodicOrthocrossing.translatePolyline
    simp only [List.getLast?_map, endpoints.2, Option.map_some]
    rw [presentation.contractedEndpointOccurrencePosition_target]
    rfl

/-- The occurrence formula is literally source template, trimmed corridor,
and reversed target template joined at their shared boundaries. -/
theorem PlanarPresentation.normalizationRouteOccurrence1_eq_threePieces
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.normalizationRouteOccurrence1 edge routeTranslate =
      joinAtEndpoint
        (presentation.firstNormalizationTemplateOccurrence
          (.source edge) routeTranslate)
        (joinAtEndpoint
          (presentation.firstNormalizationCorridorOccurrence
            edge routeTranslate)
          (presentation.firstNormalizationTemplateOccurrence
            (.target edge) routeTranslate).reverse) := by
  rw [presentation.normalizationRouteOccurrence1_eq]
  unfold normalizeRouteWithTemplates
    PlanarPresentation.firstNormalizationTemplateOccurrence
    PlanarPresentation.firstNormalizationCorridorOccurrence
  rw [presentation.contractedEndpointOccurrencePosition_source,
    presentation.contractedEndpointOccurrencePosition_target]

/-- Translation preserves the simple contracted representative at every
lattice occurrence. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_isSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    LocalIncidenceDrawing.RouteIsSimple
      (presentation.contractedEdgeRouteOccurrence edge routeTranslate) := by
  unfold PlanarPresentation.contractedEdgeRouteOccurrence
    PeriodicOrthocrossing.translatePolyline
  exact routeIsSimple_translate
    (presentation.contractedEdgeRoute_isSimple
      degree separated sourceSimple edgeMember)
    (presentation.drawing.periodTranslation routeTranslate)

/-- Translation preserves orthogonality of every contracted route
occurrence. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_orthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    OrthogonalPolyline
      (presentation.contractedEdgeRouteOccurrence edge routeTranslate) := by
  unfold PlanarPresentation.contractedEdgeRouteOccurrence
  exact (presentation.contractedEdgeRoute_orthogonal_of_mem edgeMember)
    |>.translate (presentation.drawing.periodTranslation routeTranslate)

/-- A lifted contracted route occurrence still contains a genuine edge. -/
theorem PlanarPresentation.contractedEdgeRouteOccurrence_length_ge_two
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    2 ≤ (presentation.contractedEdgeRouteOccurrence
      edge routeTranslate).length := by
  simpa [PlanarPresentation.contractedEdgeRouteOccurrence,
    PeriodicOrthocrossing.translatePolyline] using
      presentation.contractedEdgeRoute_length_ge_two degree edgeMember

private theorem routeIsSimple_scalePolyline_local
    {route : List Cell}
    {factor : Int} (factorPositive : 0 < factor)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline factor route) := by
  let geometry :
      PlanarThreeSAT.GridDrawingMap (Cell.scale factor) :=
    { injective := Cell.scale_injective factorPositive.ne'
      isAxisAligned := fun {segment} aligned => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          (GridSegment.isAxisAligned_scale_iff
            factorPositive segment).mpr aligned
      interiorContains_iff := fun {segment point} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorContains_scale_iff
            factorPositive segment point
      interiorsMeet_iff := fun {first second} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorsMeet_scale_iff
            factorPositive first second }
  exact routeIsSimple_mapPoints geometry simple

/-- Complete avoidance survives the affine ordered-unit refinement used by
`magnifiedUnitRoute`. -/
theorem magnifiedUnitRoutes_avoidEachOther
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (firstSimple : LocalIncidenceDrawing.RouteIsSimple first)
    (secondSimple : LocalIncidenceDrawing.RouteIsSimple second) :
    RoutesAvoidEachOther
      (magnifiedUnitRoute first) (magnifiedUnitRoute second) := by
  let firstScaled := translatePolyline center (scalePolyline 12 first)
  let secondScaled := translatePolyline center (scalePolyline 12 second)
  have scaledAvoid : RoutesAvoidEachOther firstScaled secondScaled := by
    exact (avoid.scalePolyline (factor := 12) (by decide)).translate center
  have firstScaledOrthogonal : OrthogonalPolyline firstScaled :=
    (firstOrthogonal.scalePolyline (by decide)).translate center
  have secondScaledOrthogonal : OrthogonalPolyline secondScaled :=
    (secondOrthogonal.scalePolyline (by decide)).translate center
  have firstScaledSimple :
      LocalIncidenceDrawing.RouteIsSimple firstScaled := by
    unfold firstScaled PeriodicOrthocrossing.translatePolyline
    exact routeIsSimple_translate
      (routeIsSimple_scalePolyline_local (by decide) firstSimple) center
  have secondScaledSimple :
      LocalIncidenceDrawing.RouteIsSimple secondScaled := by
    unfold secondScaled PeriodicOrthocrossing.translatePolyline
    exact routeIsSimple_translate
      (routeIsSimple_scalePolyline_local (by decide) secondSimple) center
  have firstScaledNonempty : firstScaled ≠ [] := by
    have firstNonempty : first ≠ [] := by
      intro empty
      simp [empty] at firstLength
    simpa [firstScaled, translatePolyline, scalePolyline] using firstNonempty
  have secondScaledNonempty : secondScaled ≠ [] := by
    have secondNonempty : second ≠ [] := by
      intro empty
      simp [empty] at secondLength
    simpa [secondScaled, translatePolyline, scalePolyline] using secondNonempty
  have subdivided := scaledAvoid.unitSubdividePolyline
    firstScaledNonempty secondScaledNonempty
    firstScaledOrthogonal secondScaledOrthogonal
    firstScaledSimple secondScaledSimple
  rw [magnifiedUnitRoute_eq_translate_scale,
    magnifiedUnitRoute_eq_translate_scale]
  simpa [firstScaled, secondScaled] using subdivided

/-- Magnifying and subdividing a simple orthogonal route produces a
duplicate-free point list. -/
theorem magnifiedUnitRoute_nodup
    {route : List Cell}
    (orthogonal : OrthogonalPolyline route)
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    (magnifiedUnitRoute route).Nodup := by
  let scaled := translatePolyline center (scalePolyline 12 route)
  have scaledOrthogonal : OrthogonalPolyline scaled :=
    (orthogonal.scalePolyline (by decide)).translate center
  have scaledSimple : LocalIncidenceDrawing.RouteIsSimple scaled := by
    unfold scaled PeriodicOrthocrossing.translatePolyline
    exact routeIsSimple_translate
      (routeIsSimple_scalePolyline_local (by decide) simple) center
  rw [magnifiedUnitRoute_eq_translate_scale]
  simpa [scaled] using
    AxisDirection.unitSubdividePolyline_nodup
      scaledOrthogonal scaledSimple

/-- Any nondegenerate orthogonal old route becomes long enough for the
three-point symmetric trim. -/
theorem magnifiedUnitRoute_length_ge_thirteen
    {route : List Cell}
    (length : 2 ≤ route.length)
    (orthogonal : OrthogonalPolyline route) :
    13 ≤ (magnifiedUnitRoute route).length := by
  obtain ⟨first, second, rest, equation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two length
  subst route
  exact magnifiedUnitRoute_cons_cons_length_ge_thirteen
    first second rest (List.isChain_cons_cons.mp orthogonal).1

/-- The two middle corridors of distinct contracted route occurrences are
strictly separated after their old permitted endpoint contacts are trimmed
away. -/
theorem PlanarPresentation.firstNormalizationCorridorOccurrences_strictlyAvoid
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {firstEdge secondEdge : ContractedEdge}
    (firstMember : firstEdge ∈ problem.contractedEdges)
    (secondMember : secondEdge ∈ problem.contractedEdges)
    (firstTranslate secondTranslate : Cell)
    (different : (firstEdge, firstTranslate) ≠
      (secondEdge, secondTranslate)) :
    RoutesStrictlyAvoidEachOther
      (presentation.firstNormalizationCorridorOccurrence
        firstEdge firstTranslate)
      (presentation.firstNormalizationCorridorOccurrence
        secondEdge secondTranslate) := by
  let firstRoute :=
    presentation.contractedEdgeRouteOccurrence firstEdge firstTranslate
  let secondRoute :=
    presentation.contractedEdgeRouteOccurrence secondEdge secondTranslate
  have avoid : RoutesAvoidEachOther firstRoute secondRoute :=
    presentation.contractedEdgeRouteOccurrences_avoidEachOther
      degree separated firstMember secondMember
      firstTranslate secondTranslate different
  have firstLength : 2 ≤ firstRoute.length :=
    presentation.contractedEdgeRouteOccurrence_length_ge_two
      degree firstMember firstTranslate
  have secondLength : 2 ≤ secondRoute.length :=
    presentation.contractedEdgeRouteOccurrence_length_ge_two
      degree secondMember secondTranslate
  have firstOrthogonal : OrthogonalPolyline firstRoute :=
    presentation.contractedEdgeRouteOccurrence_orthogonal
      firstMember firstTranslate
  have secondOrthogonal : OrthogonalPolyline secondRoute :=
    presentation.contractedEdgeRouteOccurrence_orthogonal
      secondMember secondTranslate
  have firstSimple : LocalIncidenceDrawing.RouteIsSimple firstRoute :=
    presentation.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple firstMember firstTranslate
  have secondSimple : LocalIncidenceDrawing.RouteIsSimple secondRoute :=
    presentation.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple secondMember secondTranslate
  have magnifiedAvoid := magnifiedUnitRoutes_avoidEachOther
    avoid firstLength secondLength firstOrthogonal secondOrthogonal
    firstSimple secondSimple
  have firstNodup := magnifiedUnitRoute_nodup
    firstOrthogonal firstSimple
  have secondNodup := magnifiedUnitRoute_nodup
    secondOrthogonal secondSimple
  have firstLong := magnifiedUnitRoute_length_ge_thirteen
    firstLength firstOrthogonal
  have secondLong := magnifiedUnitRoute_length_ge_thirteen
    secondLength secondOrthogonal
  change RoutesStrictlyAvoidEachOther
    ((magnifiedUnitRoute firstRoute).drop 3 |>.take
      ((magnifiedUnitRoute firstRoute).length - 6))
    ((magnifiedUnitRoute secondRoute).drop 3 |>.take
      ((magnifiedUnitRoute secondRoute).length - 6))
  exact symmetricTrims_strictlyAvoidEachOther
    magnifiedAvoid firstNodup secondNodup
    (by omega) (by omega)

end PeriodicThreeDM
end LeanTrominoes
