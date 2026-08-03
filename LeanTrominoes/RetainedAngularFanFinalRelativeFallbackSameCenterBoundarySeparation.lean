import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackSameCenterOuterSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeSourcePrefixSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeTranslatedFallbackBoundarySeparation
import LeanTrominoes.RetainedAngularFanOuterRouteTranslation

/-!
# Same-center translated fallback boundary separation

The two selected fallback boundaries each consist of a fully refined source
prefix and a policy-selected outer replacement.  Relative source planarity
separates the two prefixes, the center-independent theorem separates either
prefix from the opposite outer fan, and strict angular order separates the
two outer fans when their physical target is shared.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Translating a fully refined source prefix by the physical drawing period
is the same as translating the raw retained route before both refinements. -/
theorem retainedFinalFullyScaledSourceRoutePrefix_translate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (relativeTranslate : Cell) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let sourceTranslate :=
      (finalCoordinatedPlacement formula).translation relativeTranslate
    let physicalTranslate :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate
    translatePolyline physicalTranslate
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline retainedAngularFanSourceClearanceFactor
            rawRoute)).dropLast =
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (translatePolyline sourceTranslate rawRoute))).dropLast := by
  dsimp only
  rw [retainedFinalPhysicalTranslation_eq_refinedSourceTranslation]
  rw [scalePolyline_translatePolyline', scalePolyline_translatePolyline']
  simp only [translatePolyline, List.map_dropLast]

/-- The selected ordinary-or-delayed outer replacement commutes with the
physical period translation. -/
theorem retainedFinalCoordinatedFallbackOuterReplacement_translate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
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
    (relativeTranslate : Cell) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedFinalCoordinatedFallbackOuterReplacement
          formula literal clauseIndex literalIndex) =
      retainedFinalTranslatedFallbackOuterReplacement
        formula literal clauseIndex literalIndex relativeTranslate := by
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  let terminal :=
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
      (classifiedRetainedTerminalData (routeTerminalVector rawRoute))
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        rawRoute).getLastD (0, 0))
  let translatedCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        (translatePolyline sourceTranslate rawRoute)).getLastD (0, 0))
  have rawLength : 2 ≤ rawRoute.length := by
    simpa [rawRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have rawNonempty : rawRoute ≠ [] := by
    intro empty
    simp [empty] at rawLength
  have centersTranslate :
      Cell.add physicalTranslate center = translatedCenter := by
    dsimp only [physicalTranslate, center, translatedCenter]
    rw [retainedFinalPhysicalTranslation_eq_refinedSourceTranslation]
    rw [scalePolyline_getLastD, scalePolyline_getLastD,
      translatePolyline_getLastD sourceTranslate rawRoute rawNonempty]
    change Cell.add
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale retainedAngularFanSourceClearanceFactor
            sourceTranslate))
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale retainedAngularFanSourceClearanceFactor
            (rawRoute.getLastD (0, 0)))) =
      Cell.scale retainedTerminalFanTotalRefinement
        (Cell.scale retainedAngularFanSourceClearanceFactor
          (Cell.add sourceTranslate (rawRoute.getLastD (0, 0))))
    rw [cell_scale_add retainedAngularFanSourceClearanceFactor,
      cell_scale_add retainedTerminalFanTotalRefinement]
  change translatePolyline physicalTranslate
      (if rawRoute.dropLast.length = 1 then
        retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot
       else
        retainedTerminalFanOuterCompleteRoute center terminal slot) =
    if rawRoute.dropLast.length = 1 then
      retainedTerminalFanOuterEscapedCompleteRoute
        translatedCenter terminal slot
    else
      retainedTerminalFanOuterCompleteRoute translatedCenter terminal slot
  by_cases escaped : rawRoute.dropLast.length = 1
  · rw [if_pos escaped, if_pos escaped]
    rw [retainedTerminalFanOuterEscapedCompleteRoute_translatePolyline]
    rw [centersTranslate]
  · rw [if_neg escaped, if_neg escaped]
    rw [retainedTerminalFanOuterCompleteRoute_translatePolyline]
    rw [centersTranslate]

/-- The unshifted prefix of one failed choice strictly avoids the translated
selected outer replacement of another at every nonzero period shift. -/
theorem
    retainedFinalFallbackSourcePrefix_strictlyAvoids_translatedFallbackOuterReplacement_of_nonzero
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
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))).dropLast
      (retainedFinalTranslatedFallbackOuterReplacement
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate) := by
  let reverseTranslate := Cell.neg relativeTranslate
  let physicalPlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula
  let backwardsPhysical := physicalPlacement.translation reverseTranslate
  let forwardsPhysical := physicalPlacement.translation relativeTranslate
  let firstPrefix :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex))).dropLast
  let backwardsFirstPrefix :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (translatePolyline
          ((finalCoordinatedPlacement formula).translation reverseTranslate)
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex)))).dropLast
  have reverseTranslateNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply relativeTranslateNonzero
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.neg, Cell.sub] at reverseZero ⊢
    omega
  have backwards :
      RoutesStrictlyAvoidEachOther backwardsFirstPrefix
        (retainedFinalCoordinatedFallbackOuterReplacement
          formula secondLiteral secondClauseIndex secondLiteralIndex) := by
    simpa [backwardsFirstPrefix] using
      retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackOuterReplacement_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember firstClauseMember
        secondLiteralMember firstLiteralMember secondChoiceNone
        reverseTranslate reverseTranslateNonzero
  have backwardsPrefixEq :
      translatePolyline backwardsPhysical firstPrefix =
        backwardsFirstPrefix := by
    simpa [firstPrefix, backwardsFirstPrefix, backwardsPhysical,
      physicalPlacement] using
      retainedFinalFullyScaledSourceRoutePrefix_translate
        formula firstClauseIndex firstLiteralIndex reverseTranslate
  have shifted := backwards.translatePolyline forwardsPhysical
  rw [← backwardsPrefixEq, translatePolyline_add] at shifted
  have shiftCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, physicalPlacement,
      reverseTranslate, PeriodicVariablePlacement.translation,
      Cell.neg, Cell.sub, Cell.add, Cell.scale]
  rw [shiftCancel, translatePolyline_zero,
    retainedFinalCoordinatedFallbackOuterReplacement_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      relativeTranslate] at shifted
  simpa [firstPrefix, forwardsPhysical, physicalPlacement] using shifted

/-- Two failed-choice fallback boundaries are strictly separated across a
nonzero shift when their translated target centers coincide. -/
theorem
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_translated_of_sameCenter
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
      (retainedFinalCoordinatedFallbackBoundaryPrefix
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate) := by
  let firstPrefix :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula firstClauseIndex firstLiteralIndex))).dropLast
  let translatedSecondPrefix :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (translatePolyline
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex)))).dropLast
  let firstOuter :=
    retainedFinalCoordinatedFallbackOuterReplacement
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let translatedSecondOuter :=
    retainedFinalTranslatedFallbackOuterReplacement
      formula secondLiteral secondClauseIndex secondLiteralIndex
      relativeTranslate
  have prefixesAvoid :
      RoutesStrictlyAvoidEachOther firstPrefix translatedSecondPrefix := by
    have unscaled :=
      finalCoordinatedSourceRoutePrefixes_strictlyAvoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero
    have scaled := unscaled.scalePolyline
      (factor :=
        ((retainedTerminalFanTotalRefinement *
          retainedAngularFanSourceClearanceFactor : Nat) : Int))
      (by
        norm_num [retainedTerminalFanTotalRefinement_eq,
          retainedAngularFanSourceClearanceFactor_eq])
    rw [← scalePolyline_dropLast_eq,
      ← scalePolyline_dropLast_eq] at scaled
    dsimp only [firstPrefix, translatedSecondPrefix]
    rw [scalePolyline_scalePolyline_nat,
      scalePolyline_scalePolyline_nat]
    exact scaled
  have firstPrefixAvoidSecondOuter :
      RoutesStrictlyAvoidEachOther firstPrefix translatedSecondOuter := by
    simpa [firstPrefix, translatedSecondOuter] using
      retainedFinalFallbackSourcePrefix_strictlyAvoids_translatedFallbackOuterReplacement_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember secondChoiceNone
        relativeTranslate relativeTranslateNonzero
  have secondPrefixAvoidFirstOuter :
      RoutesStrictlyAvoidEachOther translatedSecondPrefix firstOuter := by
    simpa [translatedSecondPrefix, firstOuter] using
      retainedFinalTranslatedFallbackSourcePrefix_strictlyAvoids_fallbackOuterReplacement_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        relativeTranslate relativeTranslateNonzero
  have outersAvoid :
      RoutesStrictlyAvoidEachOther firstOuter translatedSecondOuter := by
    simpa [firstOuter, translatedSecondOuter] using
      retainedFinalCoordinatedFallbackOuterReplacement_strictlyAvoids_translated_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        secondChoiceNone relativeTranslate relativeTranslateNonzero
        centersEqual
  have firstPrefixAvoidSecondBoundary :
      RoutesStrictlyAvoidEachOther firstPrefix
        (retainedFinalTranslatedFallbackBoundaryPrefix
          formula secondLiteral secondClauseIndex secondLiteralIndex
          relativeTranslate) := by
    exact
      strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        secondChoiceNone relativeTranslate firstPrefix
        (by simpa [translatedSecondPrefix] using prefixesAvoid)
        (by simpa [translatedSecondOuter] using firstPrefixAvoidSecondOuter)
  have firstOuterAvoidSecondBoundary :
      RoutesStrictlyAvoidEachOther firstOuter
        (retainedFinalTranslatedFallbackBoundaryPrefix
          formula secondLiteral secondClauseIndex secondLiteralIndex
          relativeTranslate) := by
    exact
      strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        secondChoiceNone relativeTranslate firstOuter
        (by simpa [translatedSecondPrefix] using
          secondPrefixAvoidFirstOuter.symm)
        (by simpa [translatedSecondOuter] using outersAvoid)
  exact
    (strictlyAvoids_retainedFinalCoordinatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      firstChoiceNone
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate)
      (by simpa [firstPrefix] using firstPrefixAvoidSecondBoundary.symm)
      (by simpa [firstOuter] using firstOuterAvoidSecondBoundary.symm)).symm

end PeriodicOrthocrossing
end LeanTrominoes
