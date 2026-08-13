/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalSourceRouteOtherTranslatedVertexSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackCycleSeparation

/-!
# Relative fallback-source/cycle separation

This file lifts the failed direct-selector branch of the final fixed-eight
router against implication cycles in arbitrary period cells.  Its generic
assembly theorem accepts source-prefix and discarded-final-segment
avoidance for an arbitrary physical target point; the periodic source
lemmas then instantiate that point with a translated cycle center.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Assemble a final failed-choice occurrence away from an arbitrary
radius-96 point neighborhood, given avoidance by its retained raw prefix and
discarded final segment. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_pointNeighborhood
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
    (target : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal ≠ target)
    (prefixAvoid :
      (∀ point ∈
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).dropLast,
          point ≠ target) ∧
        ∀ segment ∈
          gridPolylineSegments
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex).dropLast,
          segment.IsAxisAligned → ¬segment.Contains target)
    (finalAvoid :
      (⟨polylineLastEntrance
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex),
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned ∧
      ¬(⟨polylineLastEntrance
            (finalCoordinatedSourceRoutes
              formula clauseIndex literalIndex),
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).getLastD (0, 0)⟩ :
        GridSegment).Contains target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              target))
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
  let order := angularOccurrenceOrder source.erase routes
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  change
    (∀ point ∈ rawRoute.dropLast, point ≠ target) ∧
      ∀ segment ∈ gridPolylineSegments rawRoute.dropLast,
        segment.IsAxisAligned → ¬segment.Contains target
    at prefixAvoid
  change
    (⟨polylineLastEntrance rawRoute,
        rawRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned ∧
      ¬(⟨polylineLastEntrance rawRoute,
          rawRoute.getLastD (0, 0)⟩ : GridSegment).Contains target
    at finalAvoid
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let scaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor rawRoute
  let scaledTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor rawTerminal
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
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
      (angularFanBoundaryPositionAt placement literal.atom
        (incidenceRelativeOffset scaledClause literal)
        (angularOccurrenceIndex order literal
          clauseIndex literalIndex))
  have factorPositive :
      0 < retainedAngularFanSourceClearanceFactor := by native_decide
  have clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor := by native_decide
  have rawLength : 2 ≤ rawRoute.length := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have rawClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector rawRoute) = some rawTerminal := by
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
          (routeTerminalVector scaledRoute) = some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal, rawRoute, rawTerminal] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have scaledOrthogonal : OrthogonalPolyline scaledRoute := by
    simpa [scaledRoute, rawRoute] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
  have scaledRetained : RetainedRayPolyline scaledRoute := by
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
  have scaledCentersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement scaledClause literal ≠
        Cell.scale retainedAngularFanSourceClearanceFactor target := by
    intro scaledEqual
    apply centersDifferent
    apply Cell.scale_injective
      (show
        (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
        exact_mod_cast ne_of_gt factorPositive)
    simpa [placement, scaledClause,
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
      using scaledEqual
  have suffixHead : suffix.head? = some boundaryPoint := by
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
            (angularFanBoundaryOffset slot.val)) = boundaryPoint := by
    simpa [source, placement, routes, order,
      rawRoute, scaledRoute, scaledClause, slot,
      boundaryPoint] using
      finalCoordinatedFallbackBoundaryPoint_eq_scaledOccurrenceBoundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  by_cases prefixLength : rawRoute.dropLast.length = 1
  · have escapedValid :=
      retainedAngularFanEscapedSplicedBoundaryRoute_valid
        scaledRoute scaledTerminal slot
        scaledLength scaledClassified scaledRetained
        scaledHead escapeFits
    have escapedLast : escapedPrefix.getLast? = some boundaryPoint := by
      rw [show escapedPrefix =
        retainedAngularFanEscapedSplicedBoundaryRoute
          scaledRoute scaledTerminal slot by rfl]
      rw [escapedValid.2.1, boundaryPointEq]
    have escapedAvoid :
        RoutesStrictlyAvoidEachOther
          (joinAtEndpoint escapedPrefix suffix) nearby :=
      retainedAngularFanSourceScaledEscapedSplicedOccurrenceRoute_strictlyAvoids_otherPointNeighborhood
        placement order scaledClause literal
        clauseIndex literalIndex factorPositive clearance
        rawRoute rawTerminal slot rawLength rawClassified
        scaledOrthogonal escapeFits target
        prefixAvoid.1 prefixAvoid.2 finalAvoid.1 finalAvoid.2
        scaledCentersDifferent nearby nearbyBounded
        boundaryPoint escapedLast suffixHead
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
        scaledClause.literals[literalIndex]? = some literal := by
      simpa [scaledClause] using
        (List.mem_zipIdx_iff_getElem?
          (x := (literal, literalIndex))
          (l := clause.literals)).mp literalMember
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
        formula clauseIndex literalIndex scaledClause literal
        choiceNone prefixLength clauseLookup literalLookup]
    simpa [retainedFinalEscapedFallbackOccurrenceRoute,
      source, placement, routes, order, scaledClause,
      rawRoute, rawTerminal, scaledRoute, scaledTerminal,
      slot, escapedPrefix, suffix] using escapedAvoid
  · have ordinaryValid :=
      retainedAngularFanSplicedBoundaryRoute_valid
        scaledRoute scaledTerminal slot
        scaledLength scaledClassified scaledRetained scaledHead
    have ordinaryLast :
        ordinaryPrefix.getLast? = some boundaryPoint := by
      rw [show ordinaryPrefix =
        retainedAngularFanSplicedBoundaryRoute
          scaledRoute scaledTerminal slot by rfl]
      rw [ordinaryValid.2.1, boundaryPointEq]
    have ordinaryAvoid :
        RoutesStrictlyAvoidEachOther
          (joinAtEndpoint ordinaryPrefix suffix) nearby :=
      retainedAngularFanSourceScaledSplicedOccurrenceRoute_strictlyAvoids_otherPointNeighborhood
        placement order scaledClause literal
        clauseIndex literalIndex factorPositive clearance
        rawRoute rawTerminal slot rawLength rawClassified
        scaledOrthogonal target
        prefixAvoid.1 prefixAvoid.2 finalAvoid.1 finalAvoid.2
        scaledCentersDifferent nearby nearbyBounded
        boundaryPoint ordinaryLast suffixHead
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
        formula clauseIndex literalIndex choiceNone prefixLength,
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember]
    simpa [ordinaryPrefix, suffix, scaledRoute,
      scaledTerminal, rawRoute, rawTerminal, slot,
      source, placement, routes, order, scaledClause] using ordinaryAvoid

/-- A failed-choice occurrence is strictly separated from a translated
flattened implication cycle whose translated source center differs from its
own canonical endpoint. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_translatedAllCycleRoute_of_center_ne
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
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal ≠
        Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let target :=
    Cell.add
      ((finalCoordinatedPlacement formula).position metadata.atom)
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
  let cycleRoute :=
    translatePolyline
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (allCycleRoutes source placement
          cycleIndex cycleLiteralIndex))
  have targetAtomMemberScaled :
      metadata.atom ∈ sourceVariables source.erase :=
    allCycleClauseMetadata_lookup_atom_mem
      source placement metadataLookup
  have targetAtomMember :
      metadata.atom ∈
        sourceVariables (finalCoordinatedSource formula).erase := by
    simpa only [source,
      PositionedPeriodicCNF.erase_scale] using
      targetAtomMemberScaled
  have prefixAvoid :=
    finalCoordinatedSourceRoutePrefix_avoids_translatedSourceVariablePosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadata.atom targetAtomMember relativeTranslate centersDifferent
  have finalAvoid :=
    finalCoordinatedFallbackSourceRoute_finalSegment_avoids_translatedSourceVariablePosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone
      metadata.atom targetAtomMember relativeTranslate centersDifferent
  have cycleBounded :
      ∀ point ∈ cycleRoute,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor) target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor) target))
          point := by
    intro point pointMember
    apply inClosedGridRectangle_coordinateRadius_mono
      (smaller := 48) (larger := 96)
    · simpa [source, placement, target, cycleRoute] using
        retainedFinalTranslatedSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
          formula metadataLookup cycleLiteralIndex
          relativeTranslate pointMember
    · omega
  simpa [source, placement, target, cycleRoute] using
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_pointNeighborhood
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone
      target (by simpa [target] using centersDifferent)
      (by simpa [target] using prefixAvoid)
      (by simpa [target] using finalAvoid)
      cycleRoute cycleBounded

/-- At an equal translated center, a failed-choice occurrence reuses its
certified local matching-cycle separation theorem. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_translatedAllCycleRoute_of_center_eq
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
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal =
          Cell.add
            ((finalCoordinatedPlacement formula).position metadata.atom)
            ((finalCoordinatedPlacement formula).translation
              relativeTranslate)) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      localClauseMember⟩
  have routeEqual :=
    retainedFinalScaledTranslatedAllCycleRoute_eq_matchingCycleLift_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadataLookup cycleLiteralIndex relativeTranslate
      (centersEqual metadata metadataLookup)
  have localClauseIndexLt :
      metadata.localClauseIndex < presentedCycleVertices.length :=
    positionedCycleClause_localIndex_lt
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember
  have localLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClauseEqual] using cycleLiteralMember
  have cycleLiteralIndexLt : cycleLiteralIndex < 2 :=
    positionedCycleClause_literalIndex_lt_two
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember localLiteralMember
  have avoids :=
    retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_matchingCycleLift
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone
      metadata.localClauseIndex cycleLiteralIndex
      localClauseIndexLt cycleLiteralIndexLt
  rw [routeEqual]
  exact avoids

/-- Every failed-choice occurrence avoids every periodically translated
genuine flattened implication-cycle route. -/
theorem
    retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_translatedAllCycleRoute
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
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, _metadataClauseEqual,
      _localClauseMember⟩
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal =
        Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
  · exact
      retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_translatedAllCycleRoute_of_center_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        cycleClauseMember cycleLiteralMember relativeTranslate
        (fun otherMetadata otherLookup => by
          have metadataEqual : otherMetadata = metadata :=
            Option.some.inj (otherLookup.symm.trans metadataLookup)
          rw [metadataEqual]
          exact centersEqual)
  · exact
      (retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_translatedAllCycleRoute_of_center_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember choiceNone
        metadataLookup cycleLiteralIndex
        relativeTranslate centersEqual).toRoutesAvoidEachOther

/-- Every copied-source incidence route, whether selected by the direct
atlas or by either fallback branch, avoids every translated genuine cycle
route. -/
theorem
    retainedFinalCoordinatedSourceRoute_avoids_translatedAllCycleRoute
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
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  cases choiceEq :
      retainedFinalDirectSourceRouteChoice?
        formula clauseIndex literalIndex with
  | none =>
      exact
        retainedFinalCoordinatedFallbackOccurrenceRoute_avoids_translatedAllCycleRoute
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember choiceEq
          cycleClauseMember cycleLiteralMember relativeTranslate
  | some choice =>
      exact
        retainedFinalCoordinatedDirectSourceRoute_avoids_translatedAllCycleRoute
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice
          clauseMember literalMember choiceEq
          cycleClauseMember cycleLiteralMember relativeTranslate

end PeriodicOrthocrossing
end LeanTrominoes
