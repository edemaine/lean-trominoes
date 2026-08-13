/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalPortGeometry
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings

/-!
# Separation of incident carrier lenses and bend corners

When a complete carrier link and a route-bend corner share a terminal, the
terminal-port geometry identifies their external and internal boundary
certificates.  This file applies the generic boundary separator to every
genuine local incidence selected from the two actual final-variable
drawings.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The four ways a complete carrier link can share a terminal with a route
bend. -/
def CarrierLinkIncidentToRouteBend
    (link : EqualityLink CarrierNode) (routeBend : RouteBend) : Prop :=
  link.first = .terminal routeBend.incomingTerminal ∨
    link.first = .terminal routeBend.outgoingTerminal ∨
      link.second = .terminal routeBend.incomingTerminal ∨
        link.second = .terminal routeBend.outgoingTerminal

/-- Every genuine route selected from an incident carrier lens avoids every
genuine route selected from the bend-corner drawing. -/
theorem drawingPlanarSATCarrierBendRoutesAvoidEachOther_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {routeBend : RouteBend}
    (routeBendMember :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup)
    (incident : CarrierLinkIncidentToRouteBend link routeBend)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {bendClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {bendClauseIndex : Nat}
    (bendClauseMember :
      (bendClause, bendClauseIndex) ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).formula.zipIdx)
    {bendLiteral : PlanarSATVariable Variable × Bool}
    {bendLiteralIndex : Nat}
    (bendLiteralMember :
      (bendLiteral, bendLiteralIndex) ∈
        bendClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATBendCornerIncidenceDrawing
        formula routeBend).routes
          bendClauseIndex bendLiteralIndex) := by
  let graph := PeriodicCNF.incidenceGraph formula
  have geometry :
      routeBend.CornerGeometry :=
    drawingRouteBendDedup_cornerGeometry
      wellFormed degree isLocal routeBendMember
  rcases incident with
      firstIncoming |
      firstOutgoing |
      secondIncoming |
      secondOutgoing
  · have interface :=
      drawingCompleteCarrierLink_first_incomingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry firstIncoming
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
        wellFormed degree isLocal linkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        routeBend.incomingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierBounded
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideIncoming
          formula routeBend)
        carrierContacts
        (drawingPlanarSATBendCornerIncidenceDrawing_routeContactsAt_incoming
          formula routeBend)
        carrierClauseMember carrierLiteralMember
        bendClauseMember bendLiteralMember
  · have interface :=
      drawingCompleteCarrierLink_first_outgoingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry firstOutgoing
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
        wellFormed degree isLocal linkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        routeBend.outgoingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierBounded
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideOutgoing
          formula routeBend)
        carrierContacts
        (drawingPlanarSATBendCornerIncidenceDrawing_routeContactsAt_outgoing
          formula routeBend)
        carrierClauseMember carrierLiteralMember
        bendClauseMember bendLiteralMember
  · have interface :=
      drawingCompleteCarrierLink_second_incomingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry secondIncoming
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
        wellFormed degree isLocal linkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        routeBend.incomingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierBounded
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideIncoming
          formula routeBend)
        carrierContacts
        (drawingPlanarSATBendCornerIncidenceDrawing_routeContactsAt_incoming
          formula routeBend)
        carrierClauseMember carrierLiteralMember
        bendClauseMember bendLiteralMember
  · have interface :=
      drawingCompleteCarrierLink_second_outgoingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry secondOutgoing
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
        wellFormed degree isLocal linkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        routeBend.outgoingPort
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        carrierBounded
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideOutgoing
          formula routeBend)
        carrierContacts
        (drawingPlanarSATBendCornerIncidenceDrawing_routeContactsAt_outgoing
          formula routeBend)
        carrierClauseMember carrierLiteralMember
        bendClauseMember bendLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
