import LeanTrominoes.RetainedAngularFanFinalRelativeTranslatedFallbackBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackCycleSeparation
import LeanTrominoes.OrthogonalPolylineMiddleCoarsening

/-!
# Relative mixed occurrence-route separation

The two direct-prefix interactions with a translated fallback occurrence are
handled by the translated boundary and suffix theorems.  For the direct
suffix, translate it backward into the fallback source cell.  The complete
fallback occurrence then avoids its radius-96 neighborhood by the generic
source-point theorem; translating both routes forward closes both remaining
piece interactions simultaneously.
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

/-- Reversing a relative shift reverses the distinct-center relation. -/
private theorem reverseCanonicalCentersDifferent
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (firstLiteral secondLiteral : PeriodicLiteral Variable)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement secondClause secondLiteral)
          (placement.translation relativeTranslate)) :
    PositionedPeriodicCNF.canonicalLiteralPosition
        placement secondClause secondLiteral ≠
      Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral)
        (placement.translation (Cell.neg relativeTranslate)) := by
  intro reverseEqual
  apply centersDifferent
  rcases firstCenterEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
        placement firstClause firstLiteral with
    ⟨firstX, firstY⟩
  rcases secondCenterEq :
      PositionedPeriodicCNF.canonicalLiteralPosition
        placement secondClause secondLiteral with
    ⟨secondX, secondY⟩
  rcases relativeTranslate with ⟨translateX, translateY⟩
  simp [firstCenterEq, secondCenterEq,
    PeriodicVariablePlacement.translation,
    Cell.neg, Cell.sub, Cell.add, Cell.scale] at reverseEqual ⊢
  omega

/-- A translated failed-choice occurrence is strictly separated from the
untranslated Figure 7 suffix at every different canonical center. -/
theorem
    retainedFinalTranslatedFallbackOccurrenceRoute_strictlyAvoids_directOccurrenceSuffix_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
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
    let directSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (directClause.scale retainedAngularFanSourceClearanceFactor)
          directLiteral directClauseIndex directLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedFinalTranslatedFallbackOccurrenceRoute
        formula fallbackClause fallbackLiteral
        fallbackClauseIndex fallbackLiteralIndex relativeTranslate)
      directSuffix := by
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
  let directSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
  let sourcePlacement := finalCoordinatedPlacement formula
  let reverseTranslate := Cell.neg relativeTranslate
  let target :=
    Cell.add
      (PositionedPeriodicCNF.canonicalLiteralPosition
        sourcePlacement directClause directLiteral)
      (sourcePlacement.translation reverseTranslate)
  let physicalPlacement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement formula
  let backwardsPhysical :=
    physicalPlacement.translation reverseTranslate
  let forwardsPhysical :=
    physicalPlacement.translation relativeTranslate
  let backwardsDirectSuffix :=
    translatePolyline backwardsPhysical directSuffix
  have reverseCentersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement fallbackClause fallbackLiteral ≠ target := by
    simpa [sourcePlacement, target, reverseTranslate] using
      reverseCanonicalCentersDifferent
        sourcePlacement directClause fallbackClause
        directLiteral fallbackLiteral relativeTranslate centersDifferent
  have prefixAvoid :=
    finalCoordinatedSourceRoutePrefix_avoids_translatedCanonicalLiteralPosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember directClauseMember
      fallbackLiteralMember directLiteralMember reverseTranslate
      (by simpa [sourcePlacement, target] using reverseCentersDifferent)
  have fallbackFinalAligned :=
    finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone
  have finalAvoid :=
    finalCoordinatedSourceRoute_finalSegment_avoids_translatedCanonicalLiteralPosition_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember directClauseMember
      fallbackLiteralMember directLiteralMember fallbackFinalAligned
      reverseTranslate
      (by simpa [sourcePlacement, target] using reverseCentersDifferent)
  have backwardsDirectSuffixBounded :
      ∀ point ∈ backwardsDirectSuffix,
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
          point := by
    intro point pointMember
    simpa [source, placement, routes, directSuffix,
      backwardsDirectSuffix, backwardsPhysical,
      physicalPlacement, sourcePlacement, target,
      reverseTranslate] using
      retainedFinalTranslatedOccurrenceSuffix_point_in_centerRectangle
        formula directClause directLiteral
        directClauseIndex directLiteralIndex reverseTranslate pointMember
  have fallbackAvoidBackwards :=
    retainedFinalCoordinatedFallbackOccurrenceRoute_strictlyAvoids_pointNeighborhood
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone target
      (by simpa [sourcePlacement, target] using reverseCentersDifferent)
      (by simpa [sourcePlacement, target] using prefixAvoid)
      (by simpa [sourcePlacement, target] using finalAvoid)
      backwardsDirectSuffix backwardsDirectSuffixBounded
  have shifted := fallbackAvoidBackwards.translatePolyline forwardsPhysical
  have shiftCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, physicalPlacement,
      reverseTranslate, PeriodicVariablePlacement.translation,
      Cell.neg, Cell.sub, Cell.add, Cell.scale]
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone relativeTranslate,
    translatePolyline_add, shiftCancel, translatePolyline_zero] at shifted
  simpa [source, placement, routes, directSuffix,
    backwardsDirectSuffix, backwardsPhysical, forwardsPhysical,
    physicalPlacement] using shifted

/-- The translated selected fallback boundary still ends at the head of its
translated unchanged suffix. -/
theorem retainedFinalTranslatedFallbackBoundaryPrefix_boundary
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
    (relativeTranslate : Cell) :
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
    let suffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex)
    let physicalTranslate :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate
    (retainedFinalTranslatedFallbackBoundaryPrefix
      formula literal clauseIndex literalIndex relativeTranslate).getLast? =
        (translatePolyline physicalTranslate suffix).head? := by
  dsimp only
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
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  have boundary :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have translated :=
    congrArg (Option.map (Cell.add physicalTranslate)) boundary
  rw [← retainedFinalCoordinatedFallbackBoundaryPrefix_translate
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty clauseMember literalMember relativeTranslate]
  simpa [suffix, physicalTranslate, translatePolyline] using translated

/-- A successful aligned direct occurrence strictly avoids a complete
translated failed-choice occurrence at every nonzero shift with a distinct
canonical target. -/
theorem
    retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceRoute
        formula fallbackClause fallbackLiteral
        fallbackClauseIndex fallbackLiteralIndex relativeTranslate) := by
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
  let directSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  let fallbackBoundary :=
    retainedFinalTranslatedFallbackBoundaryPrefix
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
      relativeTranslate
  let fallbackSuffix :=
    translatePolyline physicalTranslate
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex))
  let fallbackBoundaryPoint :=
    Cell.add physicalTranslate
      (Cell.scale retainedTerminalFanRoutingRefinement
        (angularFanBoundaryPositionAt
          placement fallbackLiteral.atom
          (incidenceRelativeOffset
            (fallbackClause.scale
              retainedAngularFanSourceClearanceFactor)
            fallbackLiteral)
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)))
  have fallbackSuffixHead :
      fallbackSuffix.head? = some fallbackBoundaryPoint := by
    simp [fallbackSuffix, fallbackBoundaryPoint,
      translatePolyline, scalePolyline,
      angularOccurrenceSuffix_head?]
  have fallbackBoundaryJoin :=
    retainedFinalTranslatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      relativeTranslate
  have fallbackBoundaryLast :
      fallbackBoundary.getLast? = some fallbackBoundaryPoint := by
    have joinEq :
        fallbackBoundary.getLast? = fallbackSuffix.head? := by
      simpa [source, placement, routes, fallbackBoundary,
        fallbackSuffix, physicalTranslate] using fallbackBoundaryJoin
    exact joinEq.trans fallbackSuffixHead
  have prefixBoundaryAvoid :=
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersDifferent
  have prefixSuffixAvoid :=
    retainedFinalCoordinatedAlignedDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_distinctCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup directAligned
      relativeTranslate centersDifferent
  have fallbackAvoidDirectSuffix :=
    retainedFinalTranslatedFallbackOccurrenceRoute_strictlyAvoids_directOccurrenceSuffix_of_distinctCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember fallbackChoiceNone
      relativeTranslate centersDifferent
  have directSuffixAvoidJoin :
      RoutesStrictlyAvoidEachOther directSuffix
        (joinAtEndpoint fallbackBoundary fallbackSuffix) := by
    simpa [source, placement, routes, directSuffix,
      fallbackBoundary, fallbackSuffix, physicalTranslate,
      retainedFinalTranslatedFallbackOccurrenceRoute] using
      fallbackAvoidDirectSuffix.symm
  have directSuffixAvoidPieces :=
    directSuffixAvoidJoin.of_join_right
      fallbackBoundaryLast fallbackSuffixHead
  have assembled :=
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_join_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup fallbackBoundary fallbackSuffix fallbackBoundaryPoint
      fallbackBoundaryLast fallbackSuffixHead
      (by simpa [fallbackBoundary] using prefixBoundaryAvoid)
      (by simpa [source, placement, routes, fallbackSuffix,
        physicalTranslate] using prefixSuffixAvoid)
      (by simpa [source, placement, routes, directSuffix] using
        directSuffixAvoidPieces.1)
      (by simpa [source, placement, routes, directSuffix] using
        directSuffixAvoidPieces.2)
  simpa [source, placement, routes, fallbackBoundary,
    fallbackSuffix, physicalTranslate,
    retainedFinalTranslatedFallbackOccurrenceRoute] using assembled

/-- Public route-family form of the aligned successful/failed relative
separation theorem. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula directClauseIndex directLiteralIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex)) := by
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup,
    ← retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup,
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone relativeTranslate]
  exact
    retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_distinctCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersDifferent

end PeriodicOrthocrossing
end LeanTrominoes
