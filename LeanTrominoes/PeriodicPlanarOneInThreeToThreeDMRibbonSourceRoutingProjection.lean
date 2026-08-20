/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting

/-! # Explicit projection of coordinated source occurrence routes -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

theorem coordinatedSourceRibbonThreeStrandRouting_route_explicit
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
      joinAtEndpoint
        (joinAtEndpoint
          (occurrenceCoordinatedRibbonVariableStub
            presentation.toPlanarIncidencePresentation entry color)
          (occurrenceRibbonCorridorCore
            presentation.toPlanarIncidencePresentation entry color))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry color) := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
