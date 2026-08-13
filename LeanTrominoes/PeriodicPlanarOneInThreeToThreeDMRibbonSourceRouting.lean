/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceEndpointFanSystemSeparation

/-!
# Coordinated source ribbon routing

This file joins the coordinated source endpoint fans to the certified ribbon
corridor cores and packages the result as the `ThreeStrandRouting` consumed
by the planar 3DM assembly.  The assembled fan-system separation certificate
then gives contact-free separation of all distinct colored occurrence routes.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The complete coordinated three-strand routing on a ribbon-ready source
presentation. -/
noncomputable def coordinatedSourceRibbonThreeStrandRouting
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation) :
    ThreeStrandRouting source.erase :=
  RibbonEndpointFanSystem.threeStrandRouting
    presentation.toContinuousPlanarIncidencePresentation
    (coordinatedSourceRibbonEndpointFanSystem
      presentation.toPlanarIncidencePresentation width compatible)

/-- The route field of the coordinated routing is the joined variable fan,
corridor core, and clause fan selected by its endpoint-fan system. -/
theorem coordinatedSourceRibbonThreeStrandRouting_route
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible).route entry color =
      RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (coordinatedSourceRibbonEndpointFanSystem
          presentation.toPlanarIncidencePresentation width compatible)
        entry color := by
  rfl

set_option maxHeartbeats 800000 in
/-- Distinct colored occurrence routes of the coordinated source routing are
strictly separated. -/
theorem coordinatedSourceRibbonThreeStrandRoutes_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (lengthGeThree :
      ∀ entry : ActiveOccurrenceEntry source.erase,
        3 ≤
          (occurrenceUnitSourceRoute
            presentation.toPlanarIncidencePresentation entry).length)
    {first second : ActiveOccurrenceEntry source.erase}
    {firstColor secondColor : WireColor}
    (different :
      RibbonStrandsDifferent first firstColor second secondColor) :
    RoutesStrictlyAvoidEachOther
      ((coordinatedSourceRibbonThreeStrandRouting
        presentation width compatible).route first firstColor)
      ((coordinatedSourceRibbonThreeStrandRouting
        presentation width compatible).route second secondColor) := by
  apply
    RibbonEndpointFanSystem.Separation.occurrenceThreeStrandRoutes_strictlyAvoidEachOther
      (coordinatedSourceRibbonEndpointFanSystemSeparation
        presentation width compatible lengthGeThree)
      different

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
