import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPortGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierWireIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossoverSeparation

/-!
# Separation of selected retained carriers from incident crossovers

At a shared crossover boundary, a selected retained lens lies on the
external side and the placed crossover lies on the internal side of the same
physical port boundary.  Endpoint-only contact then separates all genuine
route pairs.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Every genuine route selected from a selected retained carrier lens avoids
every genuine route selected from an incident crossover drawing. -/
theorem
    retainedDrawingPlanarSATCarrierCrossoverRoutesAvoidEachOther_of_incident
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
      retainedDrawingCompleteCarrierLink_firstCarrierPort_eq_boundary
        wellFormed degree isLocal carrierLinkMember firstEqual
    have originEqual :=
      retainedDrawingCompleteCarrierLink_firstCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal carrierLinkMember firstEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
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
      retainedDrawingCompleteCarrierLink_secondCarrierPort_eq_boundary
        wellFormed degree isLocal carrierLinkMember secondEqual
    have originEqual :=
      retainedDrawingCompleteCarrierLink_secondCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal carrierLinkMember secondEqual
    have carrierBounded :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
        wellFormed degree isLocal carrierLinkMember
    have carrierContacts :=
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
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
