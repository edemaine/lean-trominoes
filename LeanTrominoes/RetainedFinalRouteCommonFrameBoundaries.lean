import LeanTrominoes.RetainedFinalRouteCommonFrameBoundaryTranslation

/-!
# Carrier boundaries for arbitrary final contacts

The finite carrier-interface geometry applies to any raw retained carrier
link and any concrete direct-source drawing in the same frame.  Combining
the common-frame route selections, contact presentations, and exact endpoint
certificates therefore yields a carrier boundary for the original arbitrary
final route occurrences.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2400000

/-- Build a route boundary at the first endpoint of an arbitrary raw retained
carrier link. -/
private def carrierBoundaryOfFirst
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierRoute macrocellRoute : List Cell}
    {carrierRouteIndex macrocellRouteIndex carrierLocalClauseIndex : Nat}
    (link : EqualityLink CarrierNode)
    (rawMember :
      link ∈ retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph)
    {macrocellSource : DrawingPlanarSATClauseSource Variable}
    (carrierSelection :
      FinalGaugedFlatNormalizedRouteSelection formula
        (carrierRoute, carrierRouteIndex)
        (.carrier link carrierLocalClauseIndex))
    (macrocellSelection :
      FinalGaugedFlatNormalizedRouteSelection formula
        (macrocellRoute, macrocellRouteIndex) macrocellSource)
    (port : CornerPort)
    (origin : Cell)
    (portEq :
      EqualityLink.firstCarrierPort
          (CarrierNode.position formula.incidenceGraph) link = port)
    (originEq :
      EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position formula.incidenceGraph) link = origin)
    (macrocellBounded :
      (macrocellSource.incidenceDrawing formula).RoutePointsSatisfy
        (port.InsideCarrierBoundaryAt origin)) :
    FinalGaugedFlatNormalizedCarrierBoundary
      carrierRoute macrocellRoute := by
  have carrierBounded :=
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
      wellFormed degree isLocal rawMember
  rw [portEq, originEq] at carrierBounded
  have carrierBounded' :
      ((DrawingPlanarSATClauseSource.carrier
        link carrierLocalClauseIndex).incidenceDrawing formula
          |>.RoutePointsSatisfy
            (port.OutsideCarrierBoundaryAt origin)) := by
    simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
      carrierBounded
  exact
    FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
      carrierSelection macrocellSelection port origin
      carrierBounded' macrocellBounded

/-- Build a route boundary at the second endpoint of an arbitrary raw
retained carrier link. -/
private def carrierBoundaryOfSecond
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierRoute macrocellRoute : List Cell}
    {carrierRouteIndex macrocellRouteIndex carrierLocalClauseIndex : Nat}
    (link : EqualityLink CarrierNode)
    (rawMember :
      link ∈ retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph)
    {macrocellSource : DrawingPlanarSATClauseSource Variable}
    (carrierSelection :
      FinalGaugedFlatNormalizedRouteSelection formula
        (carrierRoute, carrierRouteIndex)
        (.carrier link carrierLocalClauseIndex))
    (macrocellSelection :
      FinalGaugedFlatNormalizedRouteSelection formula
        (macrocellRoute, macrocellRouteIndex) macrocellSource)
    (port : CornerPort)
    (origin : Cell)
    (portEq :
      EqualityLink.secondCarrierPort
          (CarrierNode.position formula.incidenceGraph) link = port)
    (originEq :
      EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position formula.incidenceGraph) link = origin)
    (macrocellBounded :
      (macrocellSource.incidenceDrawing formula).RoutePointsSatisfy
        (port.InsideCarrierBoundaryAt origin)) :
    FinalGaugedFlatNormalizedCarrierBoundary
      carrierRoute macrocellRoute := by
  have carrierBounded :=
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
      wellFormed degree isLocal rawMember
  rw [portEq, originEq] at carrierBounded
  have carrierBounded' :
      ((DrawingPlanarSATClauseSource.carrier
        link carrierLocalClauseIndex).incidenceDrawing formula
          |>.RoutePointsSatisfy
            (port.OutsideCarrierBoundaryAt origin)) := by
    simpa [DrawingPlanarSATClauseSource.incidenceDrawing] using
      carrierBounded
  exact
    FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
      carrierSelection macrocellSelection port origin
      carrierBounded' macrocellBounded

/-- An arbitrary terminal contact exposes a carrier boundary for the two
original final route occurrences. -/
theorem FinalGaugedCarrierFrameTerminalContact.exists_carrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    {carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift}
    {macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift}
    (contact :
      FinalGaugedCarrierFrameTerminalContact formula carrier macrocell) :
    Nonempty
      (FinalGaugedFlatNormalizedCarrierBoundary
        (finalGaugedRouteOccurrence formula
          carrierClauseIndex carrierLiteralIndex carrierShift)
        (finalGaugedRouteOccurrence formula
          macrocellClauseIndex macrocellLiteralIndex macrocellShift)) := by
  let relativeShift := macrocell.relativeShiftFrom carrier
  have rawMember :
      carrier.link ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph :=
    (mem_retainedDrawingCompleteCarrierLinks_iff
      formula.incidenceGraph carrier.link).mp carrier.link_mem |>.1
  have rawZero :
      carrierLinkPeriodTranslate formula.incidenceGraph
          carrier.link (0, 0) ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
    simpa using rawMember
  rcases
      carrier.exists_commonFrameRouteSelection
        formula wellFormed degree isLocal (0, 0) rawZero with
    ⟨carrierLocalClauseIndex, ⟨carrierSelection⟩⟩
  have carrierSelection' :
      FinalGaugedFlatNormalizedRouteSelection formula
        (carrier.commonFrameRoute (0, 0), carrierClauseIndex)
        (.carrier carrier.link carrierLocalClauseIndex) := by
    simpa using carrierSelection
  rcases contact.exists_commonFrameMacrocellSource formula with
    ⟨presentation⟩
  rcases presentation.exists_routeSelection formula with
    ⟨macrocellSelection⟩
  have offsetEq :=
    carrier.commonFrameOffset_zero_eq_relative macrocell
  have finish
      (commonBoundary :
        FinalGaugedFlatNormalizedCarrierBoundary
          (carrier.commonFrameRoute (0, 0))
          (macrocell.commonFrameRoute relativeShift)) :
      Nonempty
        (FinalGaugedFlatNormalizedCarrierBoundary
          (finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift)
          (finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex macrocellShift)) :=
    ⟨commonBoundary.of_commonFrame carrier macrocell
      (0, 0) relativeShift offsetEq⟩
  rcases contact with routedClauseContact | routedVariableContact
  · obtain ⟨site, occurrence, data⟩ := routedClauseContact
    have sourceEq := data.1
    have occurrenceMember := data.2.2.1
    have incident := data.2.2.2
    have macrocellBounded :
        (presentation.source.incidenceDrawing formula).RoutePointsSatisfy
          ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
            |>.InsideCarrierBoundaryAt
              (routedClauseOrigin formula site)) := by
      rw [presentation.sourceEq]
      unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
      rw [sourceEq]
      exact
        drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
          formula site
          (occurrence.sourceTerminal formula).duplicatorArm
    rcases incident with firstEqual | secondEqual
    · have interface :=
        retainedDrawingCompleteCarrierLinkRaw_first_sourceTerminalInterface
          wellFormed degree isLocal rawMember
          site occurrenceMember firstEqual
      exact finish
        (carrierBoundaryOfFirst formula wellFormed degree isLocal
          carrier.link rawMember carrierSelection' macrocellSelection
          (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
          (routedClauseOrigin formula site)
          interface.1 interface.2 macrocellBounded)
    · have interface :=
        retainedDrawingCompleteCarrierLinkRaw_second_sourceTerminalInterface
          wellFormed degree isLocal rawMember
          site occurrenceMember secondEqual
      exact finish
        (carrierBoundaryOfSecond formula wellFormed degree isLocal
          carrier.link rawMember carrierSelection' macrocellSelection
          (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
          (routedClauseOrigin formula site)
          interface.1 interface.2 macrocellBounded)
  · obtain
      ⟨site, armIndex, arm, link, localClauseIndex,
        occurrence, data⟩ := routedVariableContact
    have sourceEq := data.1
    have occurrenceMember := data.2.2.1
    have incident := data.2.2.2
    have macrocellBounded :
        (presentation.source.incidenceDrawing formula).RoutePointsSatisfy
          ((occurrence.targetTerminal formula).duplicatorArm.carrierPort
            |>.InsideCarrierBoundaryAt
              (routedVariableOrigin formula site)) := by
      rw [presentation.sourceEq]
      unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
      rw [sourceEq]
      exact
        drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_insideCarrierBoundaryAtArm
          formula site arm
          (occurrence.targetTerminal formula).duplicatorArm link
    rcases incident with firstEqual | secondEqual
    · have interface :=
        retainedDrawingCompleteCarrierLinkRaw_first_targetTerminalInterface
          wellFormed degree isLocal rawMember
          site occurrenceMember firstEqual
      exact finish
        (carrierBoundaryOfFirst formula wellFormed degree isLocal
          carrier.link rawMember carrierSelection' macrocellSelection
          (occurrence.targetTerminal formula).duplicatorArm.carrierPort
          (routedVariableOrigin formula site)
          interface.1 interface.2 macrocellBounded)
    · have interface :=
        retainedDrawingCompleteCarrierLinkRaw_second_targetTerminalInterface
          wellFormed degree isLocal rawMember
          site occurrenceMember secondEqual
      exact finish
        (carrierBoundaryOfSecond formula wellFormed degree isLocal
          carrier.link rawMember carrierSelection' macrocellSelection
          (occurrence.targetTerminal formula).duplicatorArm.carrierPort
          (routedVariableOrigin formula site)
          interface.1 interface.2 macrocellBounded)

/-- An arbitrary crossover residue exposes a carrier boundary after common
canonical normalization, then transports it back to the original routes. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.exists_crossoverCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      macrocell.metadata.source = .crossover crossing localClauseIndex)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    Nonempty
      (FinalGaugedFlatNormalizedCarrierBoundary
        (finalGaugedRouteOccurrence formula
          carrierClauseIndex carrierLiteralIndex carrierShift)
        (finalGaugedRouteOccurrence formula
          macrocellClauseIndex macrocellLiteralIndex macrocellShift)) := by
  let carrierReindex :=
    carrier.normalizedCrossoverShift macrocell crossing
  let macrocellReindex :=
    Cell.neg (crossingPeriodShift formula.incidenceGraph crossing)
  let normalizedLink :=
    carrier.normalizedCrossoverLink macrocell crossing
  let normalizedCrossing :=
    crossing.periodNormalize formula.incidenceGraph
  have centerEq : macrocell.center = crossing.point := by
    have advertised := macrocell.centerEq
    rw [sourceEq] at advertised
    simpa [DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATComponent.macrocellCenter] using
        Option.some.inj advertised.symm
  have rawMember :
      normalizedLink ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
    exact carrier.normalizedCrossoverLink_mem_raw
      wellFormed degree isLocal macrocell crossing centerEq notSeparated
  rcases
      carrier.exists_commonFrameRouteSelection
        formula wellFormed degree isLocal carrierReindex rawMember with
    ⟨carrierLocalClauseIndex, ⟨carrierSelection⟩⟩
  rcases
      macrocell.exists_normalizedCrossoverCommonFrameSource
        formula crossing localClauseIndex sourceEq with
    ⟨presentation⟩
  rcases presentation.exists_routeSelection formula with
    ⟨macrocellSelection⟩
  have incident :
      CarrierLinkIncidentToCrossover normalizedLink normalizedCrossing := by
    exact carrier.normalizedCrossoverContact
      formula wellFormed degree isLocal macrocell crossing
      localClauseIndex sourceEq notSeparated
  have offsetEq :
      carrier.commonFrameOffset carrierReindex =
        macrocell.commonFrameOffset macrocellReindex := by
    exact carrier.commonFrameOffset_normalizedCrossover_eq
      macrocell crossing
  have finish
      (commonBoundary :
        FinalGaugedFlatNormalizedCarrierBoundary
          (carrier.commonFrameRoute carrierReindex)
          (macrocell.commonFrameRoute macrocellReindex)) :
      Nonempty
        (FinalGaugedFlatNormalizedCarrierBoundary
          (finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift)
          (finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex macrocellShift)) :=
    ⟨commonBoundary.of_commonFrame carrier macrocell
      carrierReindex macrocellReindex offsetEq⟩
  rcases incident with ⟨side, firstEqual | secondEqual⟩
  · have portEq :=
      retainedDrawingCompleteCarrierLinkRaw_firstCarrierPort_eq_boundary
        wellFormed degree isLocal rawMember firstEqual
    have originEq :=
      retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal rawMember firstEqual
    have macrocellBounded :
        (presentation.source.incidenceDrawing formula).RoutePointsSatisfy
          (side.carrierPort.InsideCarrierBoundaryAt
            (crossingMacroOrigin normalizedCrossing)) := by
      rw [presentation.sourceEq]
      unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
      simp [macrocellReindex, sourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize]
      exact
        drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula normalizedCrossing side
    exact finish
      (carrierBoundaryOfFirst formula wellFormed degree isLocal
        normalizedLink rawMember carrierSelection macrocellSelection
        side.carrierPort (crossingMacroOrigin normalizedCrossing)
        portEq originEq macrocellBounded)
  · have portEq :=
      retainedDrawingCompleteCarrierLinkRaw_secondCarrierPort_eq_boundary
        wellFormed degree isLocal rawMember secondEqual
    have originEq :=
      retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_boundary
        wellFormed degree isLocal rawMember secondEqual
    have macrocellBounded :
        (presentation.source.incidenceDrawing formula).RoutePointsSatisfy
          (side.carrierPort.InsideCarrierBoundaryAt
            (crossingMacroOrigin normalizedCrossing)) := by
      rw [presentation.sourceEq]
      unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
      simp [macrocellReindex, sourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize]
      exact
        drawingPlanarSATCrossoverIncidenceDrawing_routePoints_insideCarrierBoundary
          formula normalizedCrossing side
    exact finish
      (carrierBoundaryOfSecond formula wellFormed degree isLocal
        normalizedLink rawMember carrierSelection macrocellSelection
        side.carrierPort (crossingMacroOrigin normalizedCrossing)
        portEq originEq macrocellBounded)

/-- Every overlapping selected carrier and direct macrocell occurrence has a
carrier boundary in their original arbitrary final frame. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.exists_carrierBoundary_of_direct_of_notSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift)
    (direct : macrocell.metadata.source.component.IsDirect)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    Nonempty
      (FinalGaugedFlatNormalizedCarrierBoundary
        (finalGaugedRouteOccurrence formula
          carrierClauseIndex carrierLiteralIndex carrierShift)
        (finalGaugedRouteOccurrence formula
          macrocellClauseIndex macrocellLiteralIndex macrocellShift)) := by
  rcases
      carrier.crossover_or_carrierFrameTerminalContact
        formula wellFormed degree isLocal macrocell direct notSeparated with
    crossover | terminal
  · obtain ⟨crossing, localClauseIndex, sourceEq⟩ := crossover
    exact carrier.exists_crossoverCarrierBoundary
      formula wellFormed degree isLocal macrocell
      crossing localClauseIndex sourceEq notSeparated
  · exact terminal.exists_carrierBoundary
      formula wellFormed degree isLocal

end PeriodicOrthocrossing
end LeanTrominoes
