/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceOtherSpokeSeparation
import LeanTrominoes.RetainedAngularFanFinalCrossClauseOccurrenceSuffixSeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOtherSourceNeighborhood

/-!
# Final direct prefixes avoid other shared-center occurrence suffixes

The direct-source atlas proves that a coordinated prefix avoids every
different Figure 7 spoke at its own variable center.  This file identifies
that finite spoke with the actual positioned suffix of an incidence in
another final source clause.

At a shared canonical variable center, different source clauses select
different angular slots.  The finite atlas certificate therefore transports
directly to the final occurrence family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- After the final common refinement, a direct source route's radius-288
rectangle is separated from the radius-96 neighborhood of every lattice
point outside its original endpoint rectangle. -/
theorem
    retainedDirectSource_scaledSourceRectangle_separated_pointSpokeRectangle
    (choice : RetainedDirectSourceRouteChoice)
    {point : Cell}
    (outside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        point) :
    ClosedGridRectanglesSeparated
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateLower))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          choice.sourceSegment.coordinateUpper))
      (coordinateRadiusLower 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point))
      (coordinateRadiusUpper 96
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point)) := by
  have separated :=
    ClosedGridRectanglesSeparated.scale_both_coordinateRadius
      (GridSegment.coordinateRectangle_separated_point_of_not_in
        (segment := choice.sourceSegment) outside)
      (factor := retainedTerminalFanTotalRefinement * 4)
      (radius := 288)
      (by native_decide)
      (by native_decide)
  norm_num [retainedTerminalFanTotalRefinement,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    retainedTerminalFanRoutingRefinement] at separated ⊢
  simp only [ClosedGridRectanglesSeparated,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale] at separated ⊢
  rcases separated with
      forwardX | backwardX | forwardY | backwardY
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- No genuine periodically translated literal occurrence other than the
represented endpoint can lie in a successful direct source segment's
endpoint rectangle. -/
theorem
    retainedFinalDirectSourceRouteChoice_sourceSegment_contains_only_canonicalLiteralPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    (sourceClauseIndex sourceLiteralIndex : Nat)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula sourceClauseIndex sourceLiteralIndex =
        some choice)
    {targetClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {targetClauseIndex : Nat}
    (targetClauseMember :
      (targetClause, targetClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {targetLiteral :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {targetLiteralIndex : Nat}
    (targetLiteralMember :
      (targetLiteral, targetLiteralIndex) ∈
        targetClause.literals.zipIdx)
    (bounded :
      InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          targetClause targetLiteral)) :
    PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        targetClause targetLiteral =
      choice.sourceSegment.finish := by
  let source := finalCoordinatedSource formula
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have targetAtomMember :
      targetLiteral.atom ∈ source.erase.variableOccurrences :=
    atom_mem_variableOccurrences_of_positioned_members
      source targetClauseMember targetLiteralMember
  have targetValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula targetLiteral.atom.original :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      (by
        simpa [source, finalCoordinatedSource] using
          targetAtomMember)
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula sourceClauseIndex sourceLiteralIndex
      choice choiceLookup with
    ⟨sourceData⟩
  rcases retainedFinalVariablePositionData_of_valid
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      targetLiteral.atom targetValid with
    ⟨targetData⟩
  let targetShift :=
    Cell.sub targetLiteral.offset
      (PeriodicCNF.clauseAnchor targetClause.literals)
  have targetEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          targetClause targetLiteral =
        Cell.add
          (Cell.scale planarMacroScale
            (Cell.add targetData.center
              ((drawing formula.incidenceGraph).periodTranslation
                targetShift)))
          targetData.localPosition := by
    unfold PositionedPeriodicCNF.canonicalLiteralPosition
    change
      Cell.add
          ((finalCoordinatedPlacement formula).position
            targetLiteral.atom)
          ((finalCoordinatedPlacement formula).translation
            targetShift) = _
    rw [targetData.positionEq]
    simp only [finalCoordinatedPlacement]
    rw [
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
      carrierMacroPeriodTranslation_eq_scale_periodTranslation]
    rcases targetData.center with ⟨centerX, centerY⟩
    rcases
        (drawing formula.incidenceGraph).periodTranslation
          targetShift with
      ⟨shiftX, shiftY⟩
    rcases targetData.localPosition with ⟨localX, localY⟩
    simp only [Cell.add, Cell.scale, Prod.mk.injEq]
    constructor <;> ring
  exact
    choice.sourceSegment_contains_only_retainedMacrocellPosition
      sourceData.center
      (Cell.add targetData.center
        ((drawing formula.incidenceGraph).periodTranslation
          targetShift))
      targetData.localPosition
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        targetClause targetLiteral)
      sourceData.originEq targetEq targetData.localBounds
      (fun centersEqual =>
        compatibleVariableLocalPosition_of_centerKinds_periodTranslate
          formula sourceCertificate.graphWellFormed
          sourceCertificate.graphDegreeAtMostThree
          sourceCertificate.graphIsLocal
          sourceData.centerKind targetData.centerKind
          centersEqual)
      bounded

/-- A successful direct occurrence's coordinated prefix strictly avoids
the Figure 7 suffix of an incidence in another clause at the same canonical
variable center. -/
theorem
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_crossClauseOccurrenceSuffix_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some choice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
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
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot)
      secondSuffix := by
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
  let order := angularOccurrenceOrder source.erase routes
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  let secondRawRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let secondScaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      secondRawRoute
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex)
  let secondBoundary :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement secondLiteral.atom
        (incidenceRelativeOffset
          secondScaledClause secondLiteral)
        (angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex))
  have slotsDifferent : firstSlot ≠ secondSlot := by
    simpa [firstSlot, secondSlot] using
      retainedFinalCrossClauseCoordinatedOccurrenceSlots_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual
  have localSeparated :
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute firstSlot)
        (choice.figure7Spoke secondSlot) :=
    choice.completeRoute_strictlyAvoid_otherFigure7Spoke
      firstSlot secondSlot slotsDifferent
  have secondSlotVal :
      secondSlot.val =
        angularOccurrenceIndex order
          secondLiteral secondClauseIndex secondLiteralIndex := by
    simpa [source, routes, order, secondSlot,
      finalCoordinatedSource, finalCoordinatedSourceRoutes] using
      retainedFinalCoordinatedOccurrenceSlot_val
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  have secondSuffixHead :
      secondSuffix.head? = some secondBoundary := by
    simp [secondSuffix, secondBoundary, scalePolyline]
  have secondScaledLast :
      secondScaledRoute.getLastD (0, 0) =
        Cell.scale retainedAngularFanSourceClearanceFactor
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral) := by
    have routeLast :
        secondScaledRoute.getLast? =
          some
            (Cell.scale retainedAngularFanSourceClearanceFactor
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (finalCoordinatedPlacement formula)
                secondClause secondLiteral)) := by
      simpa [secondScaledRoute, secondRawRoute] using
        finalCoordinatedScaledSourceRoute_getLast?
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondClauseMember secondLiteralMember
    simp [List.getLastD_eq_getLast?, routeLast]
  have boundaryPointEq :
      Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondScaledRoute.getLastD (0, 0)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset secondSlot.val)) =
        secondBoundary := by
    simpa [source, placement, routes, order,
      secondRawRoute, secondScaledRoute,
      secondScaledClause, secondSlot, secondBoundary] using
      finalCoordinatedFallbackBoundaryPoint_eq_scaledOccurrenceBoundary
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember
  have choiceCenter :
      Cell.add choice.origin
          ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0)) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral := by
    change
      choice.sourceSegment.finish =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral
    exact
      retainedFinalDirectSourceRouteChoice_sourceSegment_finish
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember firstLiteralMember choiceSome
  have choiceBoundary :
      (choice.completeRoute secondSlot).getLast? =
        some secondBoundary := by
    rw [
      choice.completeRoute_getLast_eq_scaledLocalLast,
      choiceCenter, centersEqual]
    apply congrArg some
    calc
      Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale 4
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (finalCoordinatedPlacement formula)
                secondClause secondLiteral)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset secondSlot.val)) =
        Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondScaledRoute.getLastD (0, 0)))
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset secondSlot.val)) := by
          rw [secondScaledLast]
          simp [retainedAngularFanSourceClearanceFactor]
      _ = secondBoundary := boundaryPointEq
  have spokeEq :
      choice.figure7Spoke secondSlot = secondSuffix := by
    exact
      choice.figure7Spoke_eq_scaledAngularOccurrenceSuffix
        placement order secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex
        secondSlot secondSlotVal
        (choiceBoundary.trans secondSuffixHead.symm)
  change
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot) secondSuffix
  rw [← spokeEq]
  exact localSeparated

/-- A distinct canonical occurrence center lies outside a successful
direct choice's original endpoint rectangle. -/
theorem
    retainedFinalDirectSourceRouteChoice_canonicalLiteralPosition_outside_of_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {sourceClause targetClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceClauseIndex targetClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (targetClauseMember :
      (targetClause, targetClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {sourceLiteral targetLiteral :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceLiteralIndex targetLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    (targetLiteralMember :
      (targetLiteral, targetLiteralIndex) ∈
        targetClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula sourceClauseIndex sourceLiteralIndex =
        some choice)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          sourceClause sourceLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          targetClause targetLiteral) :
    ¬InClosedGridRectangle
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        targetClause targetLiteral) := by
  intro bounded
  have targetEq :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_contains_only_canonicalLiteralPosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      sourceClauseIndex sourceLiteralIndex choiceLookup
      targetClauseMember targetLiteralMember bounded
  have sourceEq :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      sourceClauseMember sourceLiteralMember choiceLookup
  exact centersDifferent (sourceEq.symm.trans targetEq.symm)

/-- A successful direct occurrence's coordinated prefix strictly avoids
another occurrence's Figure 7 suffix whenever that occurrence's canonical
center lies outside the direct source segment's endpoint rectangle. -/
theorem
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_occurrenceSuffix_of_centerOutside
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (choice : RetainedDirectSourceRouteChoice)
    {secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    {secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {secondLiteralIndex : Nat}
    (firstSlot : RetainedTerminalSlot)
    (centerOutside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)) :
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
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot)
      secondSuffix := by
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
  let order := angularOccurrenceOrder source.erase routes
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  let secondCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula)
      secondClause secondLiteral
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex)
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 96
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            secondCenter))
      (secondUpper :=
        coordinateRadiusUpper 96
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            secondCenter))
  · intro point pointMember
    exact choice.completeRoute_point_in_sourceSegmentRectangle
      firstSlot pointMember
  · intro point pointMember
    change point ∈ secondSuffix at pointMember
    have bounded :=
      scaledAngularOccurrenceSuffix_point_in_centerRectangle
        placement order secondScaledClause secondLiteral
        secondClauseIndex secondLiteralIndex
        pointMember
    have suffixCenterEq :
        Cell.scale
            (retainedTerminalFanRoutingRefinement *
              PeriodicEightOccurrenceSplitPositioned.refinementScale)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement secondScaledClause secondLiteral) =
          Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            secondCenter := by
      dsimp only [placement, secondScaledClause, secondCenter]
      rw [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        Cell.scale_scale]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        retainedAngularFanSourceClearanceFactor,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
    rw [suffixCenterEq] at bounded
    exact bounded
  · exact
      retainedDirectSource_scaledSourceRectangle_separated_pointSpokeRectangle
        choice
        (by simpa [secondCenter] using centerOutside)

/-- A successful direct occurrence prefix strictly avoids the occurrence
suffix of every incidence in a different copied source clause. -/
theorem
    retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_crossClauseOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some choice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
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
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (secondClause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral secondClauseIndex secondLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute firstSlot)
      secondSuffix := by
  dsimp only
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral
  · exact
      retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_crossClauseOccurrenceSuffix_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        choiceSome clauseIndicesDifferent centersEqual
  · exact
      retainedFinalCoordinatedDirectOccurrencePrefix_strictlyAvoids_occurrenceSuffix_of_centerOutside
        formula choice
        (retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral firstClauseIndex firstLiteralIndex)
        (retainedFinalDirectSourceRouteChoice_canonicalLiteralPosition_outside_of_ne
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice
          firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember
          choiceSome centersEqual)

end PeriodicOrthocrossing
end LeanTrominoes
