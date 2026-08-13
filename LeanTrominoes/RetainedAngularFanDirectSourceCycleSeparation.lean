/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitRingSpokeCycleSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanPositionedRoutes

/-!
# Direct copied-source prefixes avoid their inner Figure 7 cycles

The coordinated direct-source atlas stops at the outer endpoint of a
Figure 7 spoke.  This module checks the complementary mixed interaction:
the whole atlas-selected outer prefix is strictly contact-free from every
implication route in the inner square around the same variable center.

The certificate is finite over the 33 direct clause shapes, their literal
entries, eight occurrence slots, nine ring clauses, and two implication
sides.  A common translation then positions it at the selected retained
component origin.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- One factor-eight implication route positioned in the inner Figure 7
square around a direct atlas entry's source-variable center. -/
def retainedDirectSourceInnerCycleRouteAt
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    List Cell :=
  translatePolyline
    (Cell.sub
      (retainedDirectSourceFanCenterAt kind index)
      (Cell.scale retainedTerminalFanRoutingRefinement (12, 12)))
    (scalePolyline retainedTerminalFanRoutingRefinement
      (cycleRoute vertex literalIndex.val))

/-- Every coordinated direct-source outer prefix is strictly contact-free
from every implication route in its own inner Figure 7 square. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_strictlyAvoids_innerCycleRoute :
    ∀ (vertex : RingVertex)
      (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (literalIndex : Fin 2),
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          kind index slot)
        (retainedDirectSourceInnerCycleRouteAt
          kind index vertex literalIndex) := by
  intro vertex
  cases vertex with
  | separator => native_decide
  | port port =>
      cases port <;> native_decide

/-- Positioning a checked direct-source choice preserves its strict
separation from the correspondingly positioned inner cycle route. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_innerCycleRoute
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (vertex : RingVertex)
    (literalIndex : Fin 2) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute slot)
      (translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceInnerCycleRouteAt
          choice.kind choice.index vertex literalIndex)) := by
  exact
    RoutesStrictlyAvoidEachOther.map_add
      (retainedDirectSourceFanCompleteRouteAt_strictlyAvoids_innerCycleRoute
        vertex choice.kind choice.index slot literalIndex)
      (retainedDirectSourceFanPositioningOffset choice.origin)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
