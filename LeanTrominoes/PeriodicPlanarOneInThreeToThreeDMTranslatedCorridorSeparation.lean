/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedAssembledRoutes

/-!
# Separation of translated ribbon corridors

The central ribbon construction is equivariant under source-lattice
translation.  Combining that fact with separation of lifted source-route
occurrences proves strict separation of every corridor core from every
nonzero period translate of another corridor core.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Translating a source center translates the corresponding colored exit
by the refined physical offset. -/
theorem ribbonMacrocellExit_add_center
    (center relative : Cell) (outgoing : AxisDirection)
    (color : WireColor) :
    ribbonMacrocellExit (Cell.add center relative) outgoing color =
      Cell.add (ribbonMacrocellOrigin center)
        (ribbonMacrocellExit relative outgoing color) := by
  rcases center with ⟨centerX, centerY⟩
  rcases relative with ⟨relativeX, relativeY⟩
  rcases standardRibbonMacrocellExit outgoing color with ⟨exitX, exitY⟩
  simp [ribbonMacrocellExit, ribbonMacrocellOrigin,
    standardThreeStrandLayout, Cell.add, Cell.scale]
  constructor <;> ring

/-- Translating every source center translates the assembled ribbon corridor
by the correspondingly refined physical offset. -/
theorem ribbonCorridorCore_translatePolyline
    (color : WireColor) (offset : Cell) (points : List Cell) :
    ribbonCorridorCore color (translatePolyline offset points) =
      translatePolyline (ribbonMacrocellOrigin offset)
        (ribbonCorridorCore color points) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [translatePolyline, ribbonCorridorCore]
  | cons_cons first second rest _ tailInduction =>
      cases rest with
      | nil =>
          simp only [translatePolyline, List.map_cons, List.map_nil,
            ribbonCorridorCore_pair]
          unfold ribbonCorridorCoreStart
          rw [AxisDirection.between_add_left,
            ribbonMacrocellExit_add_center]
      | cons next rest =>
          cases rest with
          | nil =>
              simpa [translatePolyline, ribbonCorridorCore] using
                ribbonMacrocellRoute_add_center offset second
                  (AxisDirection.between first second)
                  (AxisDirection.between second next) color
          | cons fourth rest =>
              simp only [translatePolyline, List.map_cons]
              rw [ribbonCorridorCore, ribbonCorridorCore]
              change
                joinAtEndpoint
                    (ribbonMacrocellRoute (Cell.add offset second)
                      (AxisDirection.between
                        (Cell.add offset first) (Cell.add offset second))
                      (AxisDirection.between
                        (Cell.add offset second) (Cell.add offset next)) color)
                    (ribbonCorridorCore color
                      (translatePolyline offset
                        (second :: next :: fourth :: rest))) =
                  translatePolyline (ribbonMacrocellOrigin offset)
                    (joinAtEndpoint
                      (ribbonMacrocellRoute second
                        (AxisDirection.between first second)
                        (AxisDirection.between second next) color)
                      (ribbonCorridorCore color
                        (second :: next :: fourth :: rest)))
              rw [translatePolyline_joinAtEndpoint]
              rw [AxisDirection.between_add_left,
                AxisDirection.between_add_left,
                ribbonMacrocellRoute_add_center,
                tailInduction second]
              rfl

/-- Unit source routes remain endpoint-separated after an arbitrary pair of
additional lattice translations whose lifted source-route keys differ. -/
theorem translatedOccurrenceUnitSourceRoutes_meetOnlyAtEndpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (firstTranslate secondTranslate : Cell)
    (different :
      occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation first firstTranslate ≠
        occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation second secondTranslate) :
    RoutesMeetOnlyAtEndpoints
      (translatePolyline (placement.translation firstTranslate)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first))
      (translatePolyline (placement.translation secondTranslate)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstRoute := occurrenceSourceRoute planar first
  let secondRoute := occurrenceSourceRoute planar second
  let firstOffset := placement.translation firstTranslate
  let secondOffset := placement.translation secondTranslate
  have avoid :=
    translatedOccurrenceSourceRoutes_avoidEachOther
      presentation first second firstTranslate secondTranslate different
  have subdivided :=
    routesMeetOnlyAtEndpoints_unitSubdividePolyline
      (first := translatePolyline firstOffset firstRoute)
      (second := translatePolyline secondOffset secondRoute)
      (by
        intro empty
        have originalEmpty : firstRoute = [] := by
          simpa [translatePolyline] using empty
        exact
          (List.ne_nil_of_length_pos
            (lt_of_lt_of_le (by decide)
              (occurrenceSourceRoute_length planar first))) originalEmpty)
      (by
        intro empty
        have originalEmpty : secondRoute = [] := by
          simpa [translatePolyline] using empty
        exact
          (List.ne_nil_of_length_pos
            (lt_of_lt_of_le (by decide)
              (occurrenceSourceRoute_length planar second))) originalEmpty)
      ((occurrenceSourceRoute_orthogonal planar first).translate
        firstOffset)
      ((occurrenceSourceRoute_orthogonal planar second).translate
        secondOffset)
      (by simpa [firstRoute, secondRoute, firstOffset, secondOffset] using avoid)
  simp only [translatePolyline] at subdivided
  rw [AxisDirection.unitSubdividePolyline_map_add,
    AxisDirection.unitSubdividePolyline_map_add] at subdivided
  simpa [occurrenceUnitSourceRoute, firstRoute, secondRoute,
    firstOffset, secondOffset, translatePolyline] using subdivided

/-- Corridor cores inherited from distinct lifted occurrence routes remain
strictly separated after arbitrary semantic lattice translations. -/
theorem translatedOccurrenceRibbonCorridorCores_strictlyAvoidEachOther_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (firstTranslate secondTranslate : Cell)
    (different :
      occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation first firstTranslate ≠
        occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation second secondTranslate)
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation firstTranslate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation first firstColor))
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation secondTranslate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstRoute := occurrenceUnitSourceRoute planar first
  let secondRoute := occurrenceUnitSourceRoute planar second
  let firstOffset := placement.translation firstTranslate
  let secondOffset := placement.translation secondTranslate
  change
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstOffset)
        (ribbonCorridorCore
          (routedRibbonLane source.erase first firstColor) firstRoute))
      (translatePolyline (ribbonMacrocellOrigin secondOffset)
        (ribbonCorridorCore
          (routedRibbonLane source.erase second secondColor) secondRoute))
  rw [← ribbonCorridorCore_translatePolyline,
    ← ribbonCorridorCore_translatePolyline]
  apply sourceRibbonCorridorCores_strictlyAvoidEachOther
    (translatedOccurrenceUnitSourceRoutes_meetOnlyAtEndpoints
      presentation first second firstTranslate secondTranslate different)
  · simpa [translatePolyline, firstRoute, planar] using
      (occurrenceUnitSourceRoute_nodup presentation first).map
        (Cell.add_left_injective firstOffset)
  · simpa [translatePolyline, secondRoute, planar] using
      (occurrenceUnitSourceRoute_nodup presentation second).map
        (Cell.add_left_injective secondOffset)
  · simpa [translatePolyline, firstRoute] using firstLength
  · simpa [translatePolyline, secondRoute] using secondLength
  · unfold translatePolyline
    apply List.isChain_map_of_isChain (Cell.add firstOffset)
    · intro sourcePoint targetPoint
        (unit : AxisDirection.IsUnitAxisStep sourcePoint targetPoint)
      exact AxisDirection.IsUnitAxisStep.translate unit firstOffset
    · exact occurrenceUnitSourceRoute_unitSteps planar first
  · unfold translatePolyline
    apply List.isChain_map_of_isChain (Cell.add secondOffset)
    · intro sourcePoint targetPoint
        (unit : AxisDirection.IsUnitAxisStep sourcePoint targetPoint)
      exact AxisDirection.IsUnitAxisStep.translate unit secondOffset
    · exact occurrenceUnitSourceRoute_unitSteps planar second
  · simpa [translatePolyline, firstRoute, planar] using
      (occurrenceUnitSourceRoute_hasNoImmediateReversal
        presentation.toContinuousPlanarIncidencePresentation first).translate
          firstOffset
  · simpa [translatePolyline, secondRoute, planar] using
      (occurrenceUnitSourceRoute_hasNoImmediateReversal
        presentation.toContinuousPlanarIncidencePresentation second).translate
          secondOffset

/-- Every length-three occurrence corridor core strictly avoids every
nonzero period translate of every other such core. -/
theorem occurrenceRibbonCorridorCore_strictlyAvoids_nonzeroTranslate_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    {translate : Cell} (translateNonzero : translate ≠ (0, 0))
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  simpa [PeriodicVariablePlacement.translation, ribbonMacrocellOrigin,
    Cell.scale] using
    translatedOccurrenceRibbonCorridorCores_strictlyAvoidEachOther_of_length_ge_three
      presentation first second (0, 0) translate
      (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
        presentation.toPlanarIncidencePresentation first second
        translateNonzero)
      firstLength secondLength firstColor secondColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
