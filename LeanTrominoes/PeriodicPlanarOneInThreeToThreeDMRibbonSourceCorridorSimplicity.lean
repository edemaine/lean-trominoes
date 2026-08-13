/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorSimplicity
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes

/-!
# Simplicity of source occurrence ribbon corridors

The generic corridor-simplicity theorem applies directly to the unitized,
duplicate-free, no-reversal route selected by every active occurrence of a
ribbon-ready source presentation.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- Every occurrence corridor core inherited from a ribbon-ready source is
geometrically simple. -/
theorem occurrenceRibbonCorridorCore_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  have length := occurrenceUnitSourceRoute_length planar entry
  have unitSteps := occurrenceUnitSourceRoute_unitSteps planar entry
  have noReversal :=
    occurrenceUnitSourceRoute_hasNoImmediateReversal
      presentation.toContinuousPlanarIncidencePresentation entry
  have nodup := occurrenceUnitSourceRoute_nodup presentation entry
  cases routeEquation : occurrenceUnitSourceRoute planar entry with
  | nil =>
      simp [routeEquation] at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp [routeEquation] at length
      | cons second rest =>
          have simple :=
            ribbonCorridorCore_simple
              (routedRibbonLane source.erase entry color)
              first second rest
              (by simpa [routeEquation] using unitSteps)
              (by simpa [planar, routeEquation] using noReversal)
              (by simpa [planar, routeEquation] using nodup)
          simpa [occurrenceRibbonCorridorCore,
            planar, routeEquation] using simple

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
