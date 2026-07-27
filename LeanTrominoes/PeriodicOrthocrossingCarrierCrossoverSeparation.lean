import LeanTrominoes.PeriodicOrthocrossingCarrierCrossoverPortGeometry
import LeanTrominoes.PeriodicOrthocrossingCrossoverComponentCarrierInterface
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings

/-!
# Separation of carriers from incident crossovers

At a crossover boundary shared with a retained carrier lens, the lens lies
on the external side of the exact physical port boundary while the placed
crossover lies on its internal side.  Endpoint-only contact on both drawings
therefore separates every selected genuine route pair.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A retained carrier link is incident to one crossover when either
endpoint is one of that crossover's four boundary variables. -/
def CarrierLinkIncidentToCrossover
    (link : EqualityLink CarrierNode)
    (crossing : CrossingRecord) : Prop :=
  ∃ side : CrossingSide,
    link.first = .boundary ⟨crossing, side⟩ ∨
      link.second = .boundary ⟨crossing, side⟩

/-- Every genuine route selected from a carrier lens avoids every genuine
route selected from an incident crossover drawing. -/
theorem
    drawingPlanarSATCarrierCrossoverRoutesAvoidEachOther_of_incident
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
    {crossing : CrossingRecord}
    (incident :
      CarrierLinkIncidentToCrossover carrierLink crossing)
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
    {crossoverClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {crossoverClauseIndex : Nat}
    (crossoverClauseMember :
      (crossoverClause, crossoverClauseIndex) ∈
        (drawingPlanarSATCrossoverIncidenceDrawing
          formula crossing).formula.zipIdx)
    {crossoverLiteral : PlanarSATVariable Variable × Bool}
    {crossoverLiteralIndex : Nat}
    (crossoverLiteralMember :
      (crossoverLiteral, crossoverLiteralIndex) ∈
        crossoverClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATCrossoverIncidenceDrawing
        formula crossing).routes
          crossoverClauseIndex crossoverLiteralIndex) := by
  rcases incident with ⟨side, firstEqual | secondEqual⟩
  · have portEqual :=
      drawingCompleteCarrierLink_firstCarrierPort_eq_boundary
        wellFormed degree isLocal carrierLinkMember firstEqual
    have originEqual :=
      drawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal carrierLinkMember firstEqual
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
        wellFormed degree isLocal carrierLinkMember
    rw [portEqual, originEqual] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        side.carrierPort
        (crossingMacroOrigin crossing)
        carrierBounded
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula crossing side)
        carrierContacts
        (drawingPlanarSATCrossoverIncidenceDrawing_routeContactsAt_carrierPort
          formula crossing side)
        carrierClauseMember carrierLiteralMember
        crossoverClauseMember crossoverLiteralMember
  · have portEqual :=
      drawingCompleteCarrierLink_secondCarrierPort_eq_boundary
        wellFormed degree isLocal carrierLinkMember secondEqual
    have originEqual :=
      drawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal carrierLinkMember secondEqual
    have carrierBounded :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
        wellFormed degree isLocal carrierLinkMember
    rw [portEqual, originEqual] at carrierBounded carrierContacts
    exact
      drawingRoutesAvoidEachOther_of_members_of_outside_insideCarrierBoundaryAt
        side.carrierPort
        (crossingMacroOrigin crossing)
        carrierBounded
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula crossing side)
        carrierContacts
        (drawingPlanarSATCrossoverIncidenceDrawing_routeContactsAt_carrierPort
          formula crossing side)
        carrierClauseMember carrierLiteralMember
        crossoverClauseMember crossoverLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
