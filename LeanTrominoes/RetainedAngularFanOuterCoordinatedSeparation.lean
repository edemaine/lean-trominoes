/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- The independently rasterized escaped route is the coordinated
construction specialized to its canonical one-route escape certificate. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_eq_coordinatedRasterized
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterEscapedCompleteRoute center terminal slot =
      retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
        center terminal slot
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center terminal slot) := by
  rfl

/-- To separate a default escaped complete route from a fixed route, it is
enough to check common-head-only avoidance for its first 64-block escape and
strict separation for everything after the escape checkpoint. -/
theorem
    retainedTerminalFanOuterEscapedCompleteRoute_separated_from_of_escape_head_contact
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (other : List Cell)
    (escapeAvoid :
      RoutesAvoidEachOther
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center terminal slot).route
        other)
    (escapeContactsAtHeads :
      RoutesMeetOnlyAtHeads
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center terminal slot).route
        other)
    (tailAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          center terminal slot)
        other) :
    RoutesAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot)
        other ∧
      RoutesMeetOnlyAtHeads
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot)
        other := by
  rw [
    retainedTerminalFanOuterEscapedCompleteRoute_eq_coordinatedRasterized,
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
  exact
    escapeAvoid.join_left_of_head_contact
      escapeContactsAtHeads tailAvoid
      (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
        center terminal slot).last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        center terminal slot)

/-- Replace the canonical rasterized 64-block escape by any certified
coordinated escape.  Separation of the canonical complete route supplies
separation of the unchanged complete tail, so only the replacement escape
must be checked against the other route. -/
theorem
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_strictlyAvoid_of_rasterized_escape_replacement
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot)
    (other : List Cell)
    (rasterizedAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot)
        other)
    (replacementEscapeAvoid :
      RoutesStrictlyAvoidEachOther escape.route other) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
        center terminal slot escape)
      other := by
  have rasterizedJoinedAvoid :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint
          (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
            center terminal slot).route
          (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
            center terminal slot))
        other := by
    rw [←
      retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
    rw [←
      retainedTerminalFanOuterEscapedCompleteRoute_eq_coordinatedRasterized]
    exact rasterizedAvoid
  have tailAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          center terminal slot)
        other :=
    (rasterizedJoinedAvoid.of_join_left
      (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
        center terminal slot).last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        center terminal slot)).2
  rw [
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
  exact replacementEscapeAvoid.join_left tailAvoid
    escape.last_eq
    (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
      center terminal slot)

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
