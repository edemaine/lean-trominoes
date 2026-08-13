/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedFallbackOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanSourceOtherPointSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Final fallback occurrences avoid other source neighborhoods

A failed direct choice leaves an orthogonal retained source route.  The
deleted-final-point prefix and the discarded final segment avoid every
different occurring source-variable center.  Source-clearance scaling turns
that integral point clearance into enough room for either outer-fan splice,
while the unchanged Figure 7 suffix stays in its own different macrocell.

This module first identifies the exact boundary shared by the final fallback
prefix and suffix, then instantiates the generic ordinary and escaped
point-neighborhood certificates for the public coordinated route family.
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

/-- The explicit terminal-fan endpoint of a genuine final fallback boundary
is the scaled head of its unchanged Figure 7 occurrence suffix. -/
theorem finalCoordinatedFallbackBoundaryPoint_eq_scaledOccurrenceBoundary
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
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
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
    let rawRoute :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let scaledRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        rawRoute
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    Cell.add
        (Cell.scale retainedTerminalFanTotalRefinement
          (scaledRoute.getLastD (0, 0)))
        (Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanBoundaryOffset slot.val)) =
      Cell.scale retainedTerminalFanRoutingRefinement
        (angularFanBoundaryPositionAt
          placement literal.atom
          (incidenceRelativeOffset
            (clause.scale
              retainedAngularFanSourceClearanceFactor)
            literal)
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            literal clauseIndex literalIndex)) := by
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
  let rawRoute :=
    finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex
  let scaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      rawRoute
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have routeFinal :
      scaledRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement scaledClause literal) := by
    simpa [scaledRoute, rawRoute, placement, scaledClause,
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
      using
        finalCoordinatedScaledSourceRoute_getLast?
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember
  have routeLastD :
      scaledRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement scaledClause literal := by
    simp [List.getLastD_eq_getLast?, routeFinal]
  have slotVal :
      slot.val =
        angularOccurrenceIndex order literal
          clauseIndex literalIndex := by
    simpa [source, routes, order, slot,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  rw [routeLastD,
    angularFanBoundaryPositionAt_eq_scaledCenter_add_offset,
    slotVal]
  simp only [PositionedPeriodicCNF.canonicalLiteralPosition,
    incidenceRelativeOffset]
  rcases placement.position literal.atom with ⟨x, y⟩
  rcases placement.translation
    (Cell.sub literal.offset
      (PeriodicCNF.clauseAnchor scaledClause.literals)) with
    ⟨dx, dy⟩
  rcases angularFanBoundaryOffset
    (angularOccurrenceIndex order literal
      clauseIndex literalIndex) with
    ⟨ox, oy⟩
  apply Prod.ext <;>
    simp [retainedTerminalFanTotalRefinement_eq,
      retainedTerminalFanRoutingRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      Cell.add, Cell.scale] <;>
    ring

/-- A failed-choice occurrence in the public coordinated route family is
strictly separated from every radius-96 route neighborhood centered at a
different occurring source variable.  The result covers both the ordinary
and delayed-lane fallback branches. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_otherSourceNeighborhood
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
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        (finalCoordinatedPlacement formula).position
          targetAtom)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).position
                targetAtom)))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).position
                targetAtom)))
          point) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      nearby := by
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
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  let rawRoute :=
    finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let scaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      rawRoute
  let scaledTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let target :=
    (finalCoordinatedPlacement formula).position targetAtom
  let ordinaryPrefix :=
    retainedAngularFanSplicedBoundaryRoute
      scaledRoute scaledTerminal slot
  let escapedPrefix :=
    retainedAngularFanEscapedSplicedBoundaryRoute
      scaledRoute scaledTerminal slot
  let suffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        scaledClause literal clauseIndex literalIndex)
  let boundaryPoint :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement literal.atom
        (incidenceRelativeOffset scaledClause literal)
        (angularOccurrenceIndex order literal
          clauseIndex literalIndex))
  have factorPositive :
      0 < retainedAngularFanSourceClearanceFactor := by
    native_decide
  have clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor := by
    native_decide
  have rawLength : 2 ≤ rawRoute.length := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have rawClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector rawRoute) =
        some rawTerminal := by
    simpa [rawRoute, rawTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, rawRoute] using
      finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have scaledClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal,
      rawRoute, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have scaledOrthogonal :
      OrthogonalPolyline scaledRoute := by
    simpa [scaledRoute, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have scaledRetained :
      RetainedRayPolyline scaledRoute := by
    simpa [scaledRoute, rawRoute] using
      finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have scaledHead :
      scaledRoute.head? =
        some
          (Cell.scale retainedAngularFanSourceClearanceFactor
            (PositionedPeriodicCNF.canonicalClausePosition
              (finalCoordinatedPlacement formula) clause)) := by
    simpa [scaledRoute, rawRoute] using
      finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength scaledTerminal := by
    simpa [scaledTerminal, rawTerminal, rawRoute] using
      finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have prefixAvoid :
      (∀ point ∈ rawRoute.dropLast,
          point ≠ target) ∧
        ∀ segment ∈ gridPolylineSegments rawRoute.dropLast,
          segment.IsAxisAligned →
            ¬segment.Contains target := by
    simpa [rawRoute, target] using
      finalCoordinatedSourceRoutePrefix_avoids_sourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        targetAtom targetAtomMember centersDifferent
  have finalAvoid :
      (⟨polylineLastEntrance rawRoute,
          rawRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned ∧
      ¬(⟨polylineLastEntrance rawRoute,
          rawRoute.getLastD (0, 0)⟩ :
        GridSegment).Contains target := by
    simpa [rawRoute, target] using
      finalCoordinatedFallbackSourceRoute_finalSegment_avoids_sourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        targetAtom targetAtomMember centersDifferent
  have scaledCentersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement scaledClause literal ≠
        Cell.scale retainedAngularFanSourceClearanceFactor
          target := by
    intro scaledEqual
    apply centersDifferent
    apply Cell.scale_injective
      (show
        (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
        exact_mod_cast ne_of_gt factorPositive)
    simpa [placement, scaledClause, target,
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
      using scaledEqual
  have suffixHead :
      suffix.head? = some boundaryPoint := by
    simpa [suffix, boundaryPoint, scalePolyline] using
      congrArg
        (Option.map
          (Cell.scale retainedTerminalFanRoutingRefinement))
        (angularOccurrenceSuffix_head?
          placement order scaledClause literal
          clauseIndex literalIndex)
  have boundaryPointEq :
      Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (scaledRoute.getLastD (0, 0)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val)) =
        boundaryPoint := by
    simpa [source, placement, routes, order,
      rawRoute, scaledRoute, scaledClause, slot,
      boundaryPoint] using
      finalCoordinatedFallbackBoundaryPoint_eq_scaledOccurrenceBoundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  by_cases prefixLength :
      rawRoute.dropLast.length = 1
  · have escapedValid :=
      retainedAngularFanEscapedSplicedBoundaryRoute_valid
        scaledRoute scaledTerminal slot
        scaledLength scaledClassified scaledRetained
        scaledHead escapeFits
    have escapedLast :
        escapedPrefix.getLast? =
          some boundaryPoint := by
      rw [show escapedPrefix =
        retainedAngularFanEscapedSplicedBoundaryRoute
          scaledRoute scaledTerminal slot by rfl]
      rw [escapedValid.2.1, boundaryPointEq]
    have escapedAvoid :
        RoutesStrictlyAvoidEachOther
          (joinAtEndpoint escapedPrefix suffix)
          nearby := by
      exact
        retainedAngularFanSourceScaledEscapedSplicedOccurrenceRoute_strictlyAvoids_otherPointNeighborhood
          placement order scaledClause literal
          clauseIndex literalIndex
          factorPositive clearance rawRoute rawTerminal slot
          rawLength rawClassified scaledOrthogonal escapeFits
          target prefixAvoid.1 prefixAvoid.2
          finalAvoid.1 finalAvoid.2 scaledCentersDifferent
          nearby nearbyBounded boundaryPoint
          escapedLast suffixHead
    have clauseLookup :
        finalCoordinatedScaledClause? formula clauseIndex =
          some scaledClause := by
      have rawClauseLookup :
          (finalCoordinatedSource formula).clauses[clauseIndex]? =
            some clause :=
        (List.mem_zipIdx_iff_getElem?
          (x := (clause, clauseIndex))
          (l := (finalCoordinatedSource formula).clauses)).mp
            clauseMember
      unfold finalCoordinatedScaledClause?
      rw [PositionedPeriodicCNF.scale_clauses,
        List.getElem?_map, rawClauseLookup]
      rfl
    have literalLookup :
        scaledClause.literals[literalIndex]? =
          some literal := by
      simpa [scaledClause] using
        (List.mem_zipIdx_iff_getElem?
          (x := (literal, literalIndex))
          (l := clause.literals)).mp literalMember
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
        formula clauseIndex literalIndex
        scaledClause literal choiceNone prefixLength
        clauseLookup literalLookup]
    simpa [retainedFinalEscapedFallbackOccurrenceRoute,
      source, placement, routes, order, scaledClause,
      rawRoute, rawTerminal, scaledRoute, scaledTerminal,
      slot, escapedPrefix, suffix] using escapedAvoid
  · have ordinaryValid :=
      retainedAngularFanSplicedBoundaryRoute_valid
        scaledRoute scaledTerminal slot
        scaledLength scaledClassified scaledRetained
        scaledHead
    have ordinaryLast :
        ordinaryPrefix.getLast? =
          some boundaryPoint := by
      rw [show ordinaryPrefix =
        retainedAngularFanSplicedBoundaryRoute
          scaledRoute scaledTerminal slot by rfl]
      rw [ordinaryValid.2.1, boundaryPointEq]
    have ordinaryAvoid :
        RoutesStrictlyAvoidEachOther
          (joinAtEndpoint ordinaryPrefix suffix)
          nearby := by
      exact
        retainedAngularFanSourceScaledSplicedOccurrenceRoute_strictlyAvoids_otherPointNeighborhood
          placement order scaledClause literal
          clauseIndex literalIndex
          factorPositive clearance rawRoute rawTerminal slot
          rawLength rawClassified scaledOrthogonal
          target prefixAvoid.1 prefixAvoid.2
          finalAvoid.1 finalAvoid.2 scaledCentersDifferent
          nearby nearbyBounded boundaryPoint
          ordinaryLast suffixHead
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
        formula clauseIndex literalIndex choiceNone prefixLength,
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember]
    simpa [ordinaryPrefix, suffix, scaledRoute,
      scaledTerminal, rawRoute, rawTerminal, slot,
      source, placement, routes, order, scaledClause] using
      ordinaryAvoid

end PeriodicOrthocrossing
end LeanTrominoes
