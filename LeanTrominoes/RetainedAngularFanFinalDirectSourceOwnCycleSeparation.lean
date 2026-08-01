import LeanTrominoes.RetainedAngularFanDirectSourceCompleteCycleSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitSpokeCycleSeparation

/-!
# Final direct occurrences avoid their matching periodic cycle lift

The direct-source atlas and the final occurrence suffix describe the same
scaled Figure 7 spoke.  Because a translation offset is determined by any
nonempty translated route, that spoke equality also identifies the atlas's
inner cycle with the corresponding periodically lifted positioned cycle.
The assembled atlas certificate can therefore be stated directly for the
final coordinated occurrence route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Equality of a direct choice's retained spoke with a scaled occurrence
suffix forces its total inner-cycle lookup to equal the correspondingly
lifted and scaled positioned cycle route. -/
theorem
    RetainedDirectSourceRouteChoice.innerCycleRoutes_eq_scaledTranslatedPositionedCycleRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (slotVal :
      slot.val =
        angularOccurrenceIndex order literal
          clauseIndex literalIndex)
    (spokeEqual :
      choice.figure7Spoke slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex))
    (cycleClauseIndex cycleLiteralIndex : Nat) :
    choice.innerCycleRoutes
        cycleClauseIndex cycleLiteralIndex =
      scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline
          ((placement sourcePlacement).translation
            (incidenceRelativeOffset clause literal))
          (positionedCycleRoutes sourcePlacement literal.atom
            cycleClauseIndex cycleLiteralIndex)) := by
  have translatedSpokesEqual := spokeEqual
  rw [choice.figure7Spoke_eq_translate,
    scalePolyline_angularOccurrenceSuffix_eq_translate,
    slotVal] at translatedSpokesEqual
  let localRoute :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (spokeRoute
        (angularPortOfIndex
          (angularOccurrenceIndex order literal
            clauseIndex literalIndex)))
  have localRouteNonempty : localRoute ≠ [] := by
    unfold localRoute scalePolyline
    cases angularPortOfIndex
        (angularOccurrenceIndex order literal
          clauseIndex literalIndex) <;>
      native_decide
  have offsetsEqual :
      Cell.add
          (Cell.sub
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (Cell.scale retainedTerminalFanRoutingRefinement
              (12, 12)))
          (retainedDirectSourceFanPositioningOffset
            choice.origin) =
        Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanOccurrenceOrigin sourcePlacement
            literal.atom
            (incidenceRelativeOffset clause literal)) := by
    exact
      translatePolyline_offsets_eq_of_nonempty
        _ _ localRoute localRouteNonempty
        (by simpa [localRoute] using translatedSpokesEqual)
  rw [
    scalePolyline_translatedPositionedCycleRoutes_eq_translate]
  unfold
    RetainedDirectSourceRouteChoice.innerCycleRoutes
  rw [translatePolyline_add, offsetsEqual]

/-- A final successful direct occurrence is literally the atlas's complete
Figure 7 route after identifying its retained suffix with the selected
spoke. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex =
      choice.completeFigure7Route
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex) := by
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
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have spokeEqual :
      choice.figure7Spoke slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes, slot,
      finalCoordinatedSource, finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes] using
      retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
  change
    joinAtEndpoint
        (choice.completeRoute slot)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex)) =
      choice.completeFigure7Route slot
  unfold RetainedDirectSourceRouteChoice.completeFigure7Route
  rw [spokeEqual]

/-- The final direct occurrence avoids every valid route of the periodically
lifted Figure 7 cycle that owns its selected occurrence endpoint. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_matchingCycleLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (cycleClauseIndex cycleLiteralIndex : Nat)
    (cycleClauseIndexLt :
      cycleClauseIndex < presentedCycleVertices.length)
    (cycleLiteralIndexLt : cycleLiteralIndex < 2) :
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    RoutesAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (translatePolyline
          ((PeriodicEightOccurrenceSplitPositioned.placement
              placement).translation
            (incidenceRelativeOffset
              (clause.scale
                retainedAngularFanSourceClearanceFactor)
              literal))
          (positionedCycleRoutes placement literal.atom
            cycleClauseIndex cycleLiteralIndex))) := by
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
      choice.figure7Spoke slot =
        scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement order
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex) := by
    simpa [source, placement, routes, order, slot,
      finalCoordinatedSource, finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes] using
      retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
  have cycleEqual :=
    RetainedDirectSourceRouteChoice.innerCycleRoutes_eq_scaledTranslatedPositionedCycleRoutes
      placement order
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex choice slot slotVal spokeEqual
      cycleClauseIndex cycleLiteralIndex
  have routeEqual :=
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
  dsimp only
  rw [routeEqual, ← cycleEqual]
  exact
    choice.completeFigure7Route_avoids_innerCycleRoutes
      slot cycleClauseIndex cycleLiteralIndex
      cycleClauseIndexLt cycleLiteralIndexLt

end PeriodicOrthocrossing
end LeanTrominoes
