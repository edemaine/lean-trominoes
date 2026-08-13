/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalComponentGeometry
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings

/-!
# Separation of carriers from incident terminal components

An occurrence terminal shared by a retained carrier lens and its routed
source-clause or target-variable drawing supplies one common carrier
boundary.  The lens lies on the external side and the terminal component
lies on the internal side, so every selected genuine route pair avoids
each other.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A retained carrier link is incident to one routed-variable target
terminal when either of its endpoints is that terminal. -/
def CarrierLinkIncidentToTargetTerminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (occurrence : CNFRouteOccurrence Variable) : Prop :=
  link.first =
      .terminal (occurrence.targetTerminal formula) ∨
    link.second =
      .terminal (occurrence.targetTerminal formula)

/-- A retained carrier link is incident to one routed-clause source
terminal when either of its endpoints is that terminal. -/
def CarrierLinkIncidentToSourceTerminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (occurrence : CNFRouteOccurrence Variable) : Prop :=
  link.first =
      .terminal (occurrence.sourceTerminal formula) ∨
    link.second =
      .terminal (occurrence.sourceTerminal formula)

/-- Every genuine route selected from a carrier lens avoids every genuine
route selected from an incident routed-variable arm. -/
theorem
    drawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : VariableRouteSite Variable}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    {arm : DuplicatorArm}
    (armEqual :
      arm =
        (occurrence.targetTerminal formula).duplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (incident :
      CarrierLinkIncidentToTargetTerminal
        formula carrierLink occurrence)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site arm routedLink).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedVariableIncidenceDrawing
        formula site arm routedLink).routes
          routedClauseIndex routedLiteralIndex) := by
  subst arm
  rcases incident with firstEqual | secondEqual
  · have interface :=
      drawingCompleteCarrierLink_first_targetTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember firstEqual
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
        wellFormed degree isLocal carrierLinkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierBounded
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierContacts
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routeContactsAt_carrierPort
          formula site
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember
  · have interface :=
      drawingCompleteCarrierLink_second_targetTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember secondEqual
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
        wellFormed degree isLocal carrierLinkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (occurrence.targetTerminal formula).duplicatorArm.carrierPort
        (routedVariableOrigin formula site)
        carrierBounded
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierContacts
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routeContactsAt_carrierPort
          formula site
          (occurrence.targetTerminal formula).duplicatorArm
          routedLink)
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember

/-- Every genuine route selected from a carrier lens avoids every genuine
route selected from an incident routed source clause. -/
theorem
    drawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther_of_incident
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {site : ClauseRouteSite}
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMember :
      occurrence ∈ clauseRouteOccurrencesAt formula site)
    (incident :
      CarrierLinkIncidentToSourceTerminal
        formula carrierLink occurrence)
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {routedClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {routedClauseIndex : Nat}
    (routedClauseMember :
      (routedClause, routedClauseIndex) ∈
        (drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).formula.zipIdx)
    {routedLiteral : PlanarSATVariable Variable × Bool}
    {routedLiteralIndex : Nat}
    (routedLiteralMember :
      (routedLiteral, routedLiteralIndex) ∈
        routedClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATRoutedClauseIncidenceDrawing
        formula site).routes
          routedClauseIndex routedLiteralIndex) := by
  rcases incident with firstEqual | secondEqual
  · have interface :=
      drawingCompleteCarrierLink_first_sourceTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember firstEqual
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
        wellFormed degree isLocal carrierLinkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
        (routedClauseOrigin formula site)
        carrierBounded
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        carrierContacts
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routeContactsAt_carrierPort
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember
  · have interface :=
      drawingCompleteCarrierLink_second_sourceTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember secondEqual
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
        wellFormed degree isLocal carrierLinkMember
    rw [interface.1, interface.2] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
        (routedClauseOrigin formula site)
        carrierBounded
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        carrierContacts
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routeContactsAt_carrierPort
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm)
        carrierClauseMember carrierLiteralMember
        routedClauseMember routedLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
