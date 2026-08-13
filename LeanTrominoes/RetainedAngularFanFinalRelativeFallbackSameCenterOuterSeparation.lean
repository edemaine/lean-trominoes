/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackPrefixOuterSeparation
import LeanTrominoes.RetainedAngularFanFinalStrictEscape
import LeanTrominoes.RetainedAngularFanOuterEscapedCompleteSeparation

/-!
# Same-center translated fallback outer-fan separation

Two failed-choice incidences whose variable endpoints agree after a nonzero
period translation have their occurrence slots and terminal directions in the
same strict angular order.  This file combines that order with the complete
ordinary and delayed-lane outer-fan geometry, covering all four policy pairs.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Complete ordinary outer routes are strictly separated when their slots
and terminal directions increase in the same strict order and both radial
pieces are nonempty. -/
private theorem ordinaryCompleteRoutes_strictlyAvoid_of_order
    (center : Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLt :
      firstTerminal.1.angularRank < secondTerminal.1.angularRank)
    (firstLengthPositive : 0 < firstTerminal.2)
    (secondLengthPositive : 0 < secondTerminal.2)
    (firstRadialPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal)
    (secondRadialPositive :
      0 < retainedTerminalFanOuterRadialLength secondTerminal)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanOuterCompleteRoute
        center firstTerminal firstSlot)
      (retainedTerminalFanOuterCompleteRoute
        center secondTerminal secondSlot) := by
  rcases firstTerminal with ⟨firstDirection, firstLength⟩
  rcases secondTerminal with ⟨secondDirection, secondLength⟩
  have directionsLe := Nat.le_of_lt directionsLt
  have radialRadial :=
    retainedTerminalFanOuterRadialRoutes_strictlyAvoid_of_direction_lt
      center firstDirection secondDirection firstLength secondLength
      firstSlot secondSlot directionsLt firstLengthPositive
      secondLengthPositive slotsLt
  have radialLocal :=
    retainedTerminalFanOuterRadialRoute_strictlyAvoid_laterLocal_of_positive
      center (firstDirection, firstLength) firstSlot secondSlot
      secondDirection firstRadialPositive directionsLe slotsLt
  have localRadial :=
    retainedTerminalFanOuterLocal_strictlyAvoid_laterRadialRoute_of_positive
      center firstDirection (secondDirection, secondLength)
      firstSlot secondSlot secondRadialPositive directionsLe slotsLt
  have localLocal :=
    retainedTerminalFanOuterLocalRoutesAt_strictlyAvoidEachOther
      center firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have firstCompleteAvoidRadial :=
    radialRadial.join_left localRadial
      (retainedTerminalFanOuterRadialRoute_getLast?
        center (firstDirection, firstLength) firstSlot firstLengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center firstDirection firstSlot)
  have firstCompleteAvoidLocal :=
    radialLocal.join_left localLocal
      (retainedTerminalFanOuterRadialRoute_getLast?
        center (firstDirection, firstLength) firstSlot firstLengthPositive)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center firstDirection firstSlot)
  exact firstCompleteAvoidRadial.join_right firstCompleteAvoidLocal
    (retainedTerminalFanOuterRadialRoute_getLast?
      center (secondDirection, secondLength) secondSlot secondLengthPositive)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center secondDirection secondSlot)

/-- Selecting ordinary or delayed-lane outer routes independently on two
strictly ordered terminals preserves strict separation. -/
private theorem selectedCompleteRoutes_strictlyAvoid_of_order
    (center : Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        firstTerminal.1 secondTerminal.1 firstSlot secondSlot)
    (firstLengthPositive : 0 < firstTerminal.2)
    (secondLengthPositive : 0 < secondTerminal.2)
    (firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength firstTerminal)
    (secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength secondTerminal)
    (firstEscaped secondEscaped : Prop)
    [Decidable firstEscaped] [Decidable secondEscaped] :
    RoutesStrictlyAvoidEachOther
      (if firstEscaped then
        retainedTerminalFanOuterEscapedCompleteRoute
          center firstTerminal firstSlot
       else
        retainedTerminalFanOuterCompleteRoute
          center firstTerminal firstSlot)
      (if secondEscaped then
        retainedTerminalFanOuterEscapedCompleteRoute
          center secondTerminal secondSlot
       else
        retainedTerminalFanOuterCompleteRoute
          center secondTerminal secondSlot) := by
  have escapePositive : 0 < retainedTerminalFanOuterSourceEscapeLength := by
    native_decide
  have firstRadialPositive :
      0 < retainedTerminalFanOuterRadialLength firstTerminal := by
    omega
  have secondRadialPositive :
      0 < retainedTerminalFanOuterRadialLength secondTerminal := by
    omega
  rcases angularOrder with
      ⟨slotsLt, directionsLt⟩ | ⟨slotsLt, directionsLt⟩
  · by_cases firstEscapedProof : firstEscaped <;>
      by_cases secondEscapedProof : secondEscaped <;>
      simp only [firstEscapedProof, secondEscapedProof]
    · exact
        retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center firstTerminal.1 secondTerminal.1
          firstTerminal.2 secondTerminal.2 firstSlot secondSlot
          directionsLt firstLengthPositive secondLengthPositive
          slotsLt firstEscapeStrict secondEscapeStrict
    · exact
        retainedTerminalFanOuterEscapedOrdinaryCompleteRoutes_strictlyAvoid_of_direction_lt
          center firstTerminal.1 secondTerminal.1
          firstTerminal.2 secondTerminal.2 firstSlot secondSlot
          directionsLt firstLengthPositive secondLengthPositive
          secondRadialPositive slotsLt firstEscapeStrict
    · exact
        retainedTerminalFanOuterOrdinaryEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center firstTerminal.1 secondTerminal.1
          firstTerminal.2 secondTerminal.2 firstSlot secondSlot
          directionsLt firstLengthPositive secondLengthPositive
          firstRadialPositive slotsLt secondEscapeStrict
    · exact ordinaryCompleteRoutes_strictlyAvoid_of_order
        center firstTerminal secondTerminal firstSlot secondSlot
        directionsLt firstLengthPositive secondLengthPositive
        firstRadialPositive secondRadialPositive slotsLt
  · by_cases firstEscapedProof : firstEscaped <;>
      by_cases secondEscapedProof : secondEscaped <;>
      simp only [firstEscapedProof, secondEscapedProof]
    · exact
        (retainedTerminalFanOuterEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center secondTerminal.1 firstTerminal.1
          secondTerminal.2 firstTerminal.2 secondSlot firstSlot
          directionsLt secondLengthPositive firstLengthPositive
          slotsLt secondEscapeStrict firstEscapeStrict).symm
    · exact
        (retainedTerminalFanOuterOrdinaryEscapedCompleteRoutes_strictlyAvoid_of_direction_lt
          center secondTerminal.1 firstTerminal.1
          secondTerminal.2 firstTerminal.2 secondSlot firstSlot
          directionsLt secondLengthPositive firstLengthPositive
          secondRadialPositive slotsLt firstEscapeStrict).symm
    · exact
        (retainedTerminalFanOuterEscapedOrdinaryCompleteRoutes_strictlyAvoid_of_direction_lt
          center secondTerminal.1 firstTerminal.1
          secondTerminal.2 firstTerminal.2 secondSlot firstSlot
          directionsLt secondLengthPositive firstLengthPositive
          firstRadialPositive slotsLt secondEscapeStrict).symm
    · exact (ordinaryCompleteRoutes_strictlyAvoid_of_order
        center secondTerminal firstTerminal secondSlot firstSlot
        directionsLt secondLengthPositive firstLengthPositive
        secondRadialPositive firstRadialPositive slotsLt).symm

/-- Canonically equal endpoints across a relative period shift induce equal
fully refined fan centers. -/
theorem retainedFinalFallbackTranslatedFanCenters_eq_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
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
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    let firstRoute :=
      finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex
    let translatedSecondRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula secondClauseIndex secondLiteralIndex)
    Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline retainedAngularFanSourceClearanceFactor
          firstRoute).getLastD (0, 0)) =
      Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline retainedAngularFanSourceClearanceFactor
          translatedSecondRoute).getLastD (0, 0)) := by
  dsimp only
  let firstRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  have firstEndpoint :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember).2
  have secondEndpoint :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember).2
  have firstLastD :
      firstRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral := by
    rw [List.getLastD_eq_getLast?, show firstRoute.getLast? = _ by
      simpa [firstRoute] using firstEndpoint]
    rfl
  have secondLastD :
      secondRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) secondClause secondLiteral := by
    rw [List.getLastD_eq_getLast?, show secondRoute.getLast? = _ by
      simpa [secondRoute] using secondEndpoint]
    rfl
  have secondNonempty : secondRoute ≠ [] := by
    intro empty
    change secondRoute.getLast? = _ at secondEndpoint
    rw [empty] at secondEndpoint
    simp at secondEndpoint
  have translatedCenter :
      Cell.add sourceTranslate
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral := by
    simpa [sourceTranslate, Cell.add, add_comm] using centersEqual.symm
  rw [scalePolyline_getLastD, firstLastD, scalePolyline_getLastD,
    translatePolyline_getLastD sourceTranslate secondRoute secondNonempty,
    secondLastD, translatedCenter]

/-- At a shared physical target, the two policy-selected fallback outer
replacements are strictly separated in every ordinary/escaped combination. -/
theorem
    retainedFinalCoordinatedFallbackOuterReplacement_strictlyAvoids_translated_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
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
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedFallbackOuterReplacement
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOuterReplacement
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate) := by
  let firstRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let translatedSecondRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      secondRoute
  let firstTerminal :=
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData (routeTerminalVector firstRoute))
  let secondTerminal :=
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData (routeTerminalVector secondRoute))
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        firstRoute).getLastD (0, 0))
  let secondCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        translatedSecondRoute).getLastD (0, 0))
  have centerEq : firstCenter = secondCenter := by
    simpa [firstRoute, secondRoute, translatedSecondRoute,
      firstCenter, secondCenter] using
      retainedFinalFallbackTranslatedFanCenters_eq_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember relativeTranslate centersEqual
  have angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        firstTerminal.1 secondTerminal.1 firstSlot secondSlot := by
    simpa [firstTerminal, secondTerminal, firstRoute, secondRoute,
      firstSlot, secondSlot, scaleRetainedTerminalData] using
      retainedFinalFallbackTerminalStrictAngularOrder_of_center_eq_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone secondChoiceNone relativeTranslate
        relativeTranslateNonzero centersEqual
  have firstLengthPositive : 0 < firstTerminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos
      (by
        simpa [firstTerminal, firstRoute] using
          finalCoordinatedSourceRoute_terminal_length_positive
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty firstClauseMember firstLiteralMember)
  have secondLengthPositive : 0 < secondTerminal.2 := by
    exact scaleRetainedTerminalData_length_pos
      retainedAngularFanSourceClearanceFactor_pos
      (by
        simpa [secondTerminal, secondRoute] using
          finalCoordinatedSourceRoute_terminal_length_positive
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty secondClauseMember secondLiteralMember)
  have firstEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength firstTerminal := by
    simpa [firstTerminal, firstRoute] using
      finalCoordinatedScaledSourceRoute_escapeStrict
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEscapeStrict :
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength secondTerminal := by
    simpa [secondTerminal, secondRoute] using
      finalCoordinatedScaledSourceRoute_escapeStrict
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have selectedAvoid :=
    selectedCompleteRoutes_strictlyAvoid_of_order
      firstCenter firstTerminal secondTerminal firstSlot secondSlot
      angularOrder firstLengthPositive secondLengthPositive
      firstEscapeStrict secondEscapeStrict
      (firstRoute.dropLast.length = 1)
      (secondRoute.dropLast.length = 1)
  change RoutesStrictlyAvoidEachOther
    (if firstRoute.dropLast.length = 1 then
      retainedTerminalFanOuterEscapedCompleteRoute
        firstCenter firstTerminal firstSlot
     else
      retainedTerminalFanOuterCompleteRoute
        firstCenter firstTerminal firstSlot)
    (if secondRoute.dropLast.length = 1 then
      retainedTerminalFanOuterEscapedCompleteRoute
        secondCenter secondTerminal secondSlot
     else
      retainedTerminalFanOuterCompleteRoute
        secondCenter secondTerminal secondSlot)
  rw [← centerEq]
  exact selectedAvoid

end PeriodicOrthocrossing
end LeanTrominoes
