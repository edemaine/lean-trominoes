import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalComponentSeparation

/-!
# Separation of selected retained carriers from terminal components

A selected retained lens and an incident routed-variable or routed-clause
component occupy opposite sides of their common terminal boundary and contact
it only at route endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Genuine routes of a selected retained lens avoid genuine routes of an
incident routed-variable arm. -/
theorem
    retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther_of_incident
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
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
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
      retainedDrawingCompleteCarrierLink_first_targetTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember firstEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
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
      retainedDrawingCompleteCarrierLink_second_targetTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember secondEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
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

/-- Genuine routes of a selected retained lens avoid genuine routes of an
incident routed-clause source. -/
theorem
    retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther_of_incident
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
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
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
      retainedDrawingCompleteCarrierLink_first_sourceTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember firstEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
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
      retainedDrawingCompleteCarrierLink_second_sourceTerminalInterface
        wellFormed degree isLocal carrierLinkMember
        site occurrenceMember secondEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
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
