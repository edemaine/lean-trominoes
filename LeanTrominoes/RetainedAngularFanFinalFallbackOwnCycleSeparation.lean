import LeanTrominoes.RetainedAngularFanFinalFallbackSpokeCycleIdentification
import LeanTrominoes.RetainedAngularFanFinalFallbackOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOrthogonality
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFailure
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteSimplicity

/-!
# Final fallback occurrences avoid their matching implication cycle

The generic copied-source certificate is specialized here to a genuine
incidence of the final coordinated source.  The failed direct selector
supplies orthogonality, retained planarity supplies route simplicity, and
the validated fan boundary identifies the generic centered Figure 7 spoke
and cycle with the positioned occurrence suffix and its periodic cycle lift.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A genuine final copied-source route remains simple after the
source-clearance scaling. -/
theorem finalCoordinatedScaledSourceRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  apply routeIsSimple_scalePolyline
    (by
      exact_mod_cast
        retainedAngularFanSourceClearanceFactor_pos)
  simpa only [finalCoordinatedSourceRoutes] using
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
      formula
      certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal
      retainedClausesNonempty
      (clause, clauseIndex)
      (by simpa only [finalCoordinatedSource] using clauseMember)
      (literal, literalIndex) literalMember

/-- Failure of the direct selector makes the corresponding source-scaled
route orthogonal. -/
theorem finalCoordinatedScaledFallbackSourceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    OrthogonalPolyline
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rcases
      exists_carrier_or_bend_witness_of_finalDirectSourceRouteChoice_none
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone with
    ⟨witness, sourceCases⟩
  have rawOrthogonal :
      OrthogonalPolyline
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex) := by
    rw [
      finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero]
    exact
      witness.routeOrthogonal_of_carrier_or_bend
        certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal
        sourceCases
  exact
    rawOrthogonal.scalePolyline
      (by
        exact_mod_cast
          retainedAngularFanSourceClearanceFactor_pos)

/-- The source-scaled route ends at the source-scaled canonical literal
position. -/
theorem finalCoordinatedScaledSourceRoute_getLast?
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (scalePolyline retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex)).getLast? =
      some
        (Cell.scale retainedAngularFanSourceClearanceFactor
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal)) := by
  simpa [scalePolyline] using congrArg
    (Option.map
      (Cell.scale retainedAngularFanSourceClearanceFactor))
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember).2

/-- At a genuine final occurrence, the centered fallback spoke is exactly
the retained positioned occurrence suffix. -/
theorem
    retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let finalPoint :=
      Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal)
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    retainedTerminalFanFigure7SpokeRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        slot =
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex) := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let suffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor)
        (angularOccurrenceOrder
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes formula)))
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
  have slotVal :
      slot.val =
        angularOccurrenceIndex
          (angularOccurrenceOrder
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula)))
          literal clauseIndex literalIndex := by
    simpa [slot, finalCoordinatedSource,
      finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapedValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have boundary :
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot).getLast? = suffix.head? := by
    simpa [rawRoute, rawTerminal, route, terminal, slot, suffix] using
      retainedFinalEscapedFallbackOccurrenceRoute_boundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal :
      route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeLastD : route.getLastD (0, 0) = finalPoint := by
    rw [List.getLastD_eq_getLast?, routeFinal]
    rfl
  have escapedLast :
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot).getLast? =
          some
            (Cell.add center
              (Cell.scale retainedTerminalFanRoutingRefinement
                (angularFanBoundaryOffset slot.val))) := by
    have escapedLast' := escapedValid.2.1
    change
      (retainedAngularFanEscapedSplicedBoundaryRoute
        route terminal slot).getLast? =
          some
            (Cell.add
              (Cell.scale retainedTerminalFanTotalRefinement
                (route.getLastD (0, 0)))
              (Cell.scale retainedTerminalFanRoutingRefinement
                (angularFanBoundaryOffset slot.val)))
      at escapedLast'
    rw [routeLastD] at escapedLast'
    exact escapedLast'
  have headsEqual :
      (retainedTerminalFanFigure7SpokeRouteAt center slot).head? =
        suffix.head? := by
    rw [retainedTerminalFanFigure7SpokeRouteAt_head?]
    exact escapedLast.symm.trans boundary
  simpa [center, finalPoint, slot, suffix] using
    retainedTerminalFanFigure7SpokeRouteAt_eq_scaledAngularOccurrenceSuffix
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      (angularOccurrenceOrder
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes formula)))
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex center slot slotVal headsEqual

/-- The generic centered cycle associated with a genuine final fallback is
the corresponding periodically lifted positioned implication cycle. -/
theorem
    retainedFinalFallbackInnerCycleRoutesAt_eq_matchingCycleLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (cycleClauseIndex cycleLiteralIndex : Nat) :
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let finalPoint :=
      Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal)
    retainedTerminalFanInnerCycleRoutesAt
        (Cell.scale retainedTerminalFanTotalRefinement finalPoint)
        cycleClauseIndex cycleLiteralIndex =
      scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline
          ((PeriodicEightOccurrenceSplitPositioned.placement
              placement).translation
            (incidenceRelativeOffset
              (clause.scale retainedAngularFanSourceClearanceFactor)
              literal))
          (positionedCycleRoutes placement literal.atom
            cycleClauseIndex cycleLiteralIndex)) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order :=
    angularOccurrenceOrder source.erase routes
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have slotVal :
      slot.val =
        angularOccurrenceIndex order literal
          clauseIndex literalIndex := by
    simpa [source, routes, order, slot,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement order
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes, order,
      finalPoint, center, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  simpa [placement, finalPoint, center] using
    retainedTerminalFanInnerCycleRoutesAt_eq_scaledTranslatedPositionedCycleRoutes
      placement order
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex center slot slotVal spokeEqual
      cycleClauseIndex cycleLiteralIndex

/-- The established ordinary copied-source occurrence used by a failed
direct choice avoids every route of its matching periodically lifted
implication cycle. -/
theorem
    retainedFinalOrdinaryFallbackOccurrenceRoute_avoids_matchingCycleLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (cycleClauseIndex cycleLiteralIndex : Nat)
    (cycleClauseIndexLt :
      cycleClauseIndex < presentedCycleVertices.length)
    (cycleLiteralIndexLt : cycleLiteralIndex < 2) :
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline
          ((PeriodicEightOccurrenceSplitPositioned.placement
              placement).translation
            (incidenceRelativeOffset
              (clause.scale retainedAngularFanSourceClearanceFactor)
              literal))
          (positionedCycleRoutes placement literal.atom
            cycleClauseIndex cycleLiteralIndex))) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let sourcePoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause)
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal := by
    simpa [route, terminal, rawRoute, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeHead : route.head? = some sourcePoint := by
    simpa [route, rawRoute, sourcePoint] using
      finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeOrthogonal : OrthogonalPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have retained : RetainedRayPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have radialLengthPositive :
      0 < retainedTerminalFanOuterRadialLength terminal := by
    have escapePositive :
        0 < retainedTerminalFanOuterSourceEscapeLength := by
      native_decide
    omega
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes,
      finalPoint, center, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeEqual :
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex =
        retainedAngularFanSplicedOwnFigure7Route
          route terminal slot finalPoint := by
    rw [
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember]
    unfold retainedAngularFanSplicedOwnFigure7Route
    rw [spokeEqual]
  have cycleEqual :
      retainedTerminalFanInnerCycleRoutesAt
          center cycleClauseIndex cycleLiteralIndex =
        scalePolyline retainedTerminalFanRoutingRefinement
          (translatePolyline
            ((PeriodicEightOccurrenceSplitPositioned.placement
                placement).translation
              (incidenceRelativeOffset
                (clause.scale retainedAngularFanSourceClearanceFactor)
                literal))
            (positionedCycleRoutes placement literal.atom
              cycleClauseIndex cycleLiteralIndex)) := by
    simpa [placement, finalPoint, center] using
      retainedFinalFallbackInnerCycleRoutesAt_eq_matchingCycleLift
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        cycleClauseIndex cycleLiteralIndex
  rw [routeEqual, ← cycleEqual]
  rw [
    retainedTerminalFanInnerCycleRoutesAt_eq_innerCycleRouteAt
      center cycleClauseIndex cycleLiteralIndex
      cycleClauseIndexLt cycleLiteralIndexLt]
  exact
    retainedAngularFanSplicedOwnFigure7Route_avoids_innerCycleRouteAt
      route terminal slot sourcePoint finalPoint
      (presentedCycleVertices.getD
        cycleClauseIndex .separator)
      ⟨cycleLiteralIndex, cycleLiteralIndexLt⟩
      routeLength classified simple routeHead routeFinal
      routeOrthogonal retained radialLengthPositive

/-- The delayed-lane copied-source occurrence used by the singleton failed
direct branch avoids every route of its matching periodically lifted
implication cycle. -/
theorem
    retainedFinalEscapedFallbackOccurrenceRoute_avoids_matchingCycleLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (cycleClauseIndex cycleLiteralIndex : Nat)
    (cycleClauseIndexLt :
      cycleClauseIndex < presentedCycleVertices.length)
    (cycleLiteralIndexLt : cycleLiteralIndex < 2) :
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    RoutesAvoidEachOther
      (retainedFinalEscapedFallbackOccurrenceRoute
        formula
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline
          ((PeriodicEightOccurrenceSplitPositioned.placement
              placement).translation
            (incidenceRelativeOffset
              (clause.scale retainedAngularFanSourceClearanceFactor)
              literal))
          (positionedCycleRoutes placement literal.atom
            cycleClauseIndex cycleLiteralIndex))) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let route :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let terminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let sourcePoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause)
  let finalPoint :=
    Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement finalPoint
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal := by
    simpa [route, terminal, rawRoute, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have simple : LocalIncidenceDrawing.RouteIsSimple route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_isSimple
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeHead : route.head? = some sourcePoint := by
    simpa [route, rawRoute, sourcePoint] using
      finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal : route.getLast? = some finalPoint := by
    simpa [route, rawRoute, finalPoint] using
      finalCoordinatedScaledSourceRoute_getLast?
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeOrthogonal : OrthogonalPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have retained : RetainedRayPolyline route := by
    simpa [route, rawRoute] using
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal := by
    simpa [terminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have spokeEqual :
      retainedTerminalFanFigure7SpokeRouteAt center slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes,
      finalPoint, center, slot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeEqual :
      retainedFinalEscapedFallbackOccurrenceRoute
          formula
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex =
        retainedAngularFanEscapedSplicedOwnFigure7Route
          route terminal slot finalPoint := by
    change
      joinAtEndpoint
          (retainedAngularFanEscapedSplicedBoundaryRoute
            route terminal slot)
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix placement
              (angularOccurrenceOrder source.erase routes)
              (clause.scale retainedAngularFanSourceClearanceFactor)
              literal clauseIndex literalIndex)) =
        retainedAngularFanEscapedSplicedOwnFigure7Route
          route terminal slot finalPoint
    unfold retainedAngularFanEscapedSplicedOwnFigure7Route
    rw [spokeEqual]
  have cycleEqual :
      retainedTerminalFanInnerCycleRoutesAt
          center cycleClauseIndex cycleLiteralIndex =
        scalePolyline retainedTerminalFanRoutingRefinement
          (translatePolyline
            ((PeriodicEightOccurrenceSplitPositioned.placement
                placement).translation
              (incidenceRelativeOffset
                (clause.scale retainedAngularFanSourceClearanceFactor)
                literal))
            (positionedCycleRoutes placement literal.atom
              cycleClauseIndex cycleLiteralIndex)) := by
    simpa [placement, finalPoint, center] using
      retainedFinalFallbackInnerCycleRoutesAt_eq_matchingCycleLift
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        cycleClauseIndex cycleLiteralIndex
  rw [routeEqual, ← cycleEqual]
  rw [
    retainedTerminalFanInnerCycleRoutesAt_eq_innerCycleRouteAt
      center cycleClauseIndex cycleLiteralIndex
      cycleClauseIndexLt cycleLiteralIndexLt]
  exact
    retainedAngularFanEscapedSplicedOwnFigure7Route_avoids_innerCycleRouteAt
      route terminal slot sourcePoint finalPoint
      (presentedCycleVertices.getD
        cycleClauseIndex .separator)
      ⟨cycleLiteralIndex, cycleLiteralIndexLt⟩
      routeLength classified simple routeHead routeFinal
      routeOrthogonal retained escapeFits

end PeriodicOrthocrossing
end LeanTrominoes
