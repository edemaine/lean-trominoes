import LeanTrominoes.RetainedFinalFlatNormalizedContactSeparation

/-!
# Boundary bounds at normalized final carrier contacts

The normalized carrier-contact certificate identifies one physical carrier
port shared by the retained equality lens and the direct noncarrier
component.  This file retains the pointwise half-plane bounds used by the
ordinary route-separation proof, rather than forgetting them after proving
`RoutesAvoidEachOther`.

Those bounds are the component-specific input to the refined terminal
checkpoint separator.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Two exact final route lists occupying opposite sides of one translated
carrier boundary. -/
structure FinalGaugedFlatNormalizedCarrierBoundary
    (carrierRoute macrocellRoute : List Cell) where
  port : CornerPort
  origin : Cell
  carrierOutside :
    ∀ point ∈ carrierRoute,
      port.OutsideCarrierBoundaryAt origin point
  macrocellInside :
    ∀ point ∈ macrocellRoute,
      port.InsideCarrierBoundaryAt origin point

/-- Drawing-wide point bounds specialize to the exact final route lists
selected by normalized clause and literal witnesses. -/
def FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    {carrierSource macrocellSource :
      DrawingPlanarSATClauseSource Variable}
    (carrierSelection :
      FinalGaugedFlatNormalizedRouteSelection
        formula carrierTaggedRoute carrierSource)
    (macrocellSelection :
      FinalGaugedFlatNormalizedRouteSelection
        formula macrocellTaggedRoute macrocellSource)
    (port : CornerPort)
    (origin : Cell)
    (carrierBounded :
      (carrierSource.incidenceDrawing formula).RoutePointsSatisfy
        (port.OutsideCarrierBoundaryAt origin))
    (macrocellBounded :
      (macrocellSource.incidenceDrawing formula).RoutePointsSatisfy
        (port.InsideCarrierBoundaryAt origin)) :
    FinalGaugedFlatNormalizedCarrierBoundary
      carrierTaggedRoute.1 macrocellTaggedRoute.1 where
  port := port
  origin := origin
  carrierOutside point pointMember := by
    apply carrierBounded.of_members
      carrierSelection.clauseMember
      carrierSelection.literalMember
    rw [← carrierSelection.routeEq]
    exact pointMember
  macrocellInside point pointMember := by
    apply macrocellBounded.of_members
      macrocellSelection.clauseMember
      macrocellSelection.literalMember
    rw [← macrocellSelection.routeEq]
    exact pointMember

/-- Every normalized crossover, routed-clause, or routed-variable contact
exposes one common carrier boundary with the exact final carrier route on
the outside and the exact final noncarrier route on the inside. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.exists_normalizedCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (contact :
      FinalGaugedFlatNormalizedCarrierContact
        formula carrier macrocell normalized) :
    Nonempty
      (FinalGaugedFlatNormalizedCarrierBoundary
        carrierTaggedRoute.1 macrocellTaggedRoute.1) := by
  rcases
      carrier.exists_normalizedRouteSelection
        formula wellFormed degree isLocal with
    ⟨carrierClauseIndex, ⟨carrierSelection⟩⟩
  rcases
      normalized.exists_routeSelection
        formula wellFormed degree isLocal with
    ⟨macrocellSelection⟩
  have normalizedLinkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  rcases contact with crossoverContact | terminalContact
  · rcases crossoverContact with
      ⟨crossing, localClauseIndex, sourceEq, incident⟩
    rcases incident with ⟨side, firstEqual | secondEqual⟩
    · have portEqual :=
        retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_boundary
          wellFormed degree isLocal normalizedLinkMember firstEqual
      have originEqual :=
        retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_boundary
          wellFormed degree isLocal normalizedLinkMember firstEqual
      have carrierBounded :=
        retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
          wellFormed degree isLocal normalizedLinkMember
      rw [portEqual, originEqual] at carrierBounded
      have carrierBounded' :
          ((DrawingPlanarSATClauseSource.carrier
            carrier.normalizedLink carrierClauseIndex).incidenceDrawing
              formula).RoutePointsSatisfy
            (side.carrierPort.OutsideCarrierBoundaryAt
              (crossingMacroOrigin crossing)) := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
          carrierBounded
      have macrocellBounded :
          (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
            (side.carrierPort.InsideCarrierBoundaryAt
              (crossingMacroOrigin crossing)) := by
        rw [sourceEq]
        exact
          drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
            formula crossing side
      exact ⟨
        FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
          carrierSelection macrocellSelection
          side.carrierPort (crossingMacroOrigin crossing)
          carrierBounded' macrocellBounded⟩
    · have portEqual :=
        retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_boundary
          wellFormed degree isLocal normalizedLinkMember secondEqual
      have originEqual :=
        retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_boundary
          wellFormed degree isLocal normalizedLinkMember secondEqual
      have carrierBounded :=
        retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
          wellFormed degree isLocal normalizedLinkMember
      rw [portEqual, originEqual] at carrierBounded
      have carrierBounded' :
          ((DrawingPlanarSATClauseSource.carrier
            carrier.normalizedLink carrierClauseIndex).incidenceDrawing
              formula).RoutePointsSatisfy
            (side.carrierPort.OutsideCarrierBoundaryAt
              (crossingMacroOrigin crossing)) := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
          carrierBounded
      have macrocellBounded :
          (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
            (side.carrierPort.InsideCarrierBoundaryAt
              (crossingMacroOrigin crossing)) := by
        rw [sourceEq]
        exact
          drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
            formula crossing side
      exact ⟨
        FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
          carrierSelection macrocellSelection
          side.carrierPort (crossingMacroOrigin crossing)
          carrierBounded' macrocellBounded⟩
  · rcases terminalContact with
      routedClauseContact | routedVariableContact
    · rcases routedClauseContact with
        ⟨site, occurrence, sourceEq,
          occurrenceMember, incident⟩
      rcases incident with firstEqual | secondEqual
      · have interface :=
          retainedDrawingCompleteCarrierLinkRaw_first_sourceTerminalInterface
            wellFormed degree isLocal normalizedLinkMember
            site occurrenceMember firstEqual
        have carrierBounded :=
          retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
            wellFormed degree isLocal normalizedLinkMember
        rw [interface.1, interface.2] at carrierBounded
        have carrierBounded' :
            ((DrawingPlanarSATClauseSource.carrier
              carrier.normalizedLink carrierClauseIndex).incidenceDrawing
                formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.OutsideCarrierBoundaryAt
                  (routedClauseOrigin formula site)) := by
          simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
            carrierBounded
        have macrocellBounded :
            (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.InsideCarrierBoundaryAt
                  (routedClauseOrigin formula site)) := by
          rw [sourceEq]
          exact
            drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
              formula site
              (occurrence.sourceTerminal formula).duplicatorArm
        exact ⟨
          FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
            carrierSelection macrocellSelection
            (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
            (routedClauseOrigin formula site)
            carrierBounded' macrocellBounded⟩
      · have interface :=
          retainedDrawingCompleteCarrierLinkRaw_second_sourceTerminalInterface
            wellFormed degree isLocal normalizedLinkMember
            site occurrenceMember secondEqual
        have carrierBounded :=
          retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
            wellFormed degree isLocal normalizedLinkMember
        rw [interface.1, interface.2] at carrierBounded
        have carrierBounded' :
            ((DrawingPlanarSATClauseSource.carrier
              carrier.normalizedLink carrierClauseIndex).incidenceDrawing
                formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.OutsideCarrierBoundaryAt
                  (routedClauseOrigin formula site)) := by
          simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
            carrierBounded
        have macrocellBounded :
            (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.InsideCarrierBoundaryAt
                  (routedClauseOrigin formula site)) := by
          rw [sourceEq]
          exact
            drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
              formula site
              (occurrence.sourceTerminal formula).duplicatorArm
        exact ⟨
          FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
            carrierSelection macrocellSelection
            (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
            (routedClauseOrigin formula site)
            carrierBounded' macrocellBounded⟩
    · rcases routedVariableContact with
        ⟨site, armIndex, arm, link,
          localClauseIndex, occurrence, sourceEq,
          occurrenceMember, incident⟩
      rcases incident with firstEqual | secondEqual
      · have interface :=
          retainedDrawingCompleteCarrierLinkRaw_first_targetTerminalInterface
            wellFormed degree isLocal normalizedLinkMember
            site occurrenceMember firstEqual
        have carrierBounded :=
          retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
            wellFormed degree isLocal normalizedLinkMember
        rw [interface.1, interface.2] at carrierBounded
        have carrierBounded' :
            ((DrawingPlanarSATClauseSource.carrier
              carrier.normalizedLink carrierClauseIndex).incidenceDrawing
                formula).RoutePointsSatisfy
              ((occurrence.targetTerminal formula).duplicatorArm.carrierPort
                |>.OutsideCarrierBoundaryAt
                  (routedVariableOrigin formula site)) := by
          simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
            carrierBounded
        have macrocellBounded :
            (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
              ((occurrence.targetTerminal formula).duplicatorArm.carrierPort
                |>.InsideCarrierBoundaryAt
                  (routedVariableOrigin formula site)) := by
          rw [sourceEq]
          exact
            drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
              formula site arm
              (occurrence.targetTerminal formula).duplicatorArm
              link
        exact ⟨
          FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
            carrierSelection macrocellSelection
            (occurrence.targetTerminal formula).duplicatorArm.carrierPort
            (routedVariableOrigin formula site)
            carrierBounded' macrocellBounded⟩
      · have interface :=
          retainedDrawingCompleteCarrierLinkRaw_second_targetTerminalInterface
            wellFormed degree isLocal normalizedLinkMember
            site occurrenceMember secondEqual
        have carrierBounded :=
          retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
            wellFormed degree isLocal normalizedLinkMember
        rw [interface.1, interface.2] at carrierBounded
        have carrierBounded' :
            ((DrawingPlanarSATClauseSource.carrier
              carrier.normalizedLink carrierClauseIndex).incidenceDrawing
                formula).RoutePointsSatisfy
              ((occurrence.targetTerminal formula).duplicatorArm.carrierPort
                |>.OutsideCarrierBoundaryAt
                  (routedVariableOrigin formula site)) := by
          simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
            carrierBounded
        have macrocellBounded :
            (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
              ((occurrence.targetTerminal formula).duplicatorArm.carrierPort
                |>.InsideCarrierBoundaryAt
                  (routedVariableOrigin formula site)) := by
          rw [sourceEq]
          exact
            drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
              formula site arm
              (occurrence.targetTerminal formula).duplicatorArm
              link
        exact ⟨
          FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
            carrierSelection macrocellSelection
            (occurrence.targetTerminal formula).duplicatorArm.carrierPort
            (routedVariableOrigin formula site)
            carrierBounded' macrocellBounded⟩

end PeriodicOrthocrossing
end LeanTrominoes
