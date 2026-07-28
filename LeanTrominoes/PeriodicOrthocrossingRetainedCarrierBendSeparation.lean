import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendComponentGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingRetainedRawCarrierGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierBendSeparation

/-!
# Separation of retained carriers from route bends

At any shared incoming or outgoing bend terminal, a raw retained lens
and the bend corner lie on opposite sides of their common carrier boundary
and contact it only at route endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Genuine routes of an incident raw retained lens and route-bend
corner avoid each other. -/
theorem
    retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther_of_raw_incident
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
      link ∈ retainedDrawingCompleteCarrierLinksRaw
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
      retainedDrawingCompleteCarrierLinkRaw_first_incomingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry firstIncoming
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first_of_raw
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
      retainedDrawingCompleteCarrierLinkRaw_first_outgoingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry firstOutgoing
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first_of_raw
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
      retainedDrawingCompleteCarrierLinkRaw_second_incomingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry secondIncoming
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second_of_raw
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
      retainedDrawingCompleteCarrierLinkRaw_second_outgoingInterface
        wellFormed degree isLocal linkMember
        routeBend geometry secondOutgoing
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
        wellFormed degree isLocal linkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second_of_raw
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

/-- The incident-bend separation theorem for selected representatives. -/
theorem
    retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther_of_incident
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
          bendClauseIndex bendLiteralIndex) :=
  retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther_of_raw_incident
    wellFormed degree isLocal
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph link).mp linkMember).1
      routeBendMember incident carrierClauseMember carrierLiteralMember
      bendClauseMember bendLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
