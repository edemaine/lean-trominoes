import LeanTrominoes.RetainedAngularFanOuterEscapedRoutes
import LeanTrominoes.OrthogonalPolylineMiddleCoarsening
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Separation interface for coordinated escaped outer routes

A coordinated complete route is naturally split at the end of its
clause-level 64-block escape.  Everything after that checkpoint is fixed by
the terminal datum and occurrence slot: the lane shift, remaining radial
raster, and local fan adapter.

This file packages that complete tail and reduces separation of two complete
coordinated routes to four explicit piece pairs.  The escape pair may share
its common clause head; both directed escape--tail pairs and the tail pair
must be contact-free.  The assembled routes then remain continuously
separated and can meet only at the inherited clause head.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Everything after a coordinated source escape: the shifted radial
remainder followed by the unchanged local fan adapter. -/
def retainedTerminalFanOuterCoordinatedEscapedCompleteTail
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterEscapedShiftedTail
      center terminal slot)
    (retainedTerminalFanOuterLocalRouteAt
      center terminal.1 slot)

/-- The complete tail starts at the fixed source-escape checkpoint. -/
@[simp]
theorem retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
      center terminal slot).head? =
        some
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot) := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterEscapedShiftedTail_head?
      center terminal slot)

/-- A coordinated complete route is exactly its selected source escape
joined to the terminal-and-slot-specific complete tail. -/
theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot) :
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
        center terminal slot escape =
      joinAtEndpoint escape.route
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          center terminal slot) := by
  unfold retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
    retainedTerminalFanOuterCoordinatedEscapedRadialRoute
    retainedTerminalFanOuterCoordinatedEscapedCompleteTail
  exact
    (joinAtEndpoint_assoc_of_middle_ne_nil
      (by
        intro empty
        have head :=
          retainedTerminalFanOuterEscapedShiftedTail_head?
            center terminal slot
        simp [empty] at head)).symm

/-- Four pairwise piece certificates assemble two coordinated complete
routes while preserving their common-head-only contact discipline. -/
theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoutes_separated
    (firstCenter secondCenter : Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstEscape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        firstCenter firstTerminal firstSlot)
    (secondEscape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        secondCenter secondTerminal secondSlot)
    (escapesAvoid :
      RoutesAvoidEachOther firstEscape.route secondEscape.route)
    (escapeContactsAtHeads :
      RoutesMeetOnlyAtHeads firstEscape.route secondEscape.route)
    (firstEscapeAvoidSecondTail :
      RoutesStrictlyAvoidEachOther
        firstEscape.route
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          secondCenter secondTerminal secondSlot))
    (firstTailAvoidSecondEscape :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          firstCenter firstTerminal firstSlot)
        secondEscape.route)
    (tailsAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          firstCenter firstTerminal firstSlot)
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          secondCenter secondTerminal secondSlot)) :
    RoutesAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          firstCenter firstTerminal firstSlot firstEscape)
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          secondCenter secondTerminal secondSlot secondEscape) ∧
      RoutesMeetOnlyAtHeads
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          firstCenter firstTerminal firstSlot firstEscape)
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          secondCenter secondTerminal secondSlot secondEscape) := by
  rw [
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail,
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
  exact
    escapesAvoid.join_tails_of_prefixes_meet_only_at_heads
      escapeContactsAtHeads
      firstEscapeAvoidSecondTail
      firstTailAvoidSecondEscape
      tailsAvoid
      firstEscape.last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        firstCenter firstTerminal firstSlot)
      secondEscape.last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        secondCenter secondTerminal secondSlot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
