import LeanTrominoes.RetainedAngularFanFinalRelativeMixedObliqueBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterOccurrenceSeparation

/-!
# Complete periodic oblique mixed occurrence separation

The oblique direct replacement and the translated fallback occurrence each
split at the Figure 7 boundary.  Distinct physical target centers use the
global rectangle and source-neighborhood certificates; a shared center uses
the strict angular slot order.  The standard two-by-two join theorem then
assembles the complete occurrence routes.
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

/-- A successful oblique direct occurrence strictly avoids a complete
translated failed-choice occurrence at every nonzero shift with a distinct
physical target center. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_distinctCenter
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
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
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
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
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_directSegment_not_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero centersDifferent
  have prefixSuffixAvoid :=
    retainedFinalCoordinatedObliqueDirectOccurrencePrefix_strictlyAvoids_translatedOccurrenceSuffix_of_distinctCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate centersDifferent
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

/-- At a shared physical center, the oblique direct prefix and direct suffix
both strictly avoid the translated fallback suffix. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrencePieces_strictlyAvoid_translatedFallbackSuffix_of_sameCenter
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
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
    let directSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex
    let physicalTranslate :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate
    let fallbackSuffix :=
      translatePolyline physicalTranslate
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
            fallbackLiteral fallbackClauseIndex fallbackLiteralIndex))
    RoutesStrictlyAvoidEachOther
        (choice.completeRoute directSlot) fallbackSuffix ∧
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (directClause.scale retainedAngularFanSourceClearanceFactor)
            directLiteral directClauseIndex directLiteralIndex))
        fallbackSuffix := by
  dsimp only
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackSuffix :=
    translatePolyline
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          (angularOccurrenceOrder
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula)))
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex))
  have angularOrder :=
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_directSegment_not_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero centersEqual
  have slotsDifferent : directSlot ≠ fallbackSlot :=
    directFallbackStrictAngularOrderCompatible_slots_ne
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
      directSlot fallbackSlot
      (by simpa [directSlot, fallbackSlot] using angularOrder)
  have fallbackSuffixEq :
      fallbackSuffix = choice.figure7Spoke fallbackSlot := by
    simpa [fallbackSuffix, fallbackSlot] using
      retainedFinalTranslatedFallbackOccurrenceSuffix_eq_directFigure7Spoke_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        relativeTranslate centersEqual
  have directSuffixEq :=
    retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup
  dsimp only at directSuffixEq
  constructor
  · have prefixAvoid :=
      choice.completeRoute_strictlyAvoid_otherFigure7Spoke
        directSlot fallbackSlot slotsDifferent
    rw [← fallbackSuffixEq] at prefixAvoid
    simpa [directSlot, fallbackSuffix] using prefixAvoid
  · have spokeAvoid :=
      retainedDirectSourceRouteChoice_figure7Spokes_strictlyAvoid
        choice directSlot fallbackSlot slotsDifferent
    rw [directSuffixEq, ← fallbackSuffixEq] at spokeAvoid
    simpa [directSlot, fallbackSuffix,
      finalCoordinatedSource, finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes] using spokeAvoid

/-- At a nonzero shared-center shift, the oblique direct Figure 7 suffix
strictly avoids the translated selected fallback boundary. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrenceSuffix_strictlyAvoids_translatedFallbackBoundaryPrefix_of_sameCenter
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
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
    RoutesStrictlyAvoidEachOther directSuffix
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  dsimp only
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral))
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  have angularOrder :=
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_directSegment_not_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero centersEqual
  have slotsDifferent : fallbackSlot ≠ directSlot := by
    exact
      (directFallbackStrictAngularOrderCompatible_slots_ne
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        (classifiedRetainedTerminalData
          (routeTerminalVector
            (finalCoordinatedSourceRoutes
              formula fallbackClauseIndex fallbackLiteralIndex))).1
        directSlot fallbackSlot
        (by simpa [directSlot, fallbackSlot] using angularOrder)).symm
  have localAvoid :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_otherFigure7SpokeRouteAt
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone directSlot
      (by simpa [fallbackSlot] using slotsDifferent)
  have translatedAvoid :=
    localAvoid.translatePolyline physicalTranslate
  have translatedSpokeEq :
      translatePolyline physicalTranslate
          (retainedTerminalFanFigure7SpokeRouteAt
            fallbackCenter directSlot) =
        choice.figure7Spoke directSlot := by
    simpa [physicalTranslate, fallbackCenter] using
      retainedFinalTranslatedFallbackFigure7SpokeRouteAt_eq_directFigure7Spoke_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember
        directLiteralMember choiceLookup relativeTranslate centersEqual
        directSlot
  have directSuffixEq :=
    retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup
  dsimp only at directSuffixEq
  rw [retainedFinalCoordinatedFallbackBoundaryPrefix_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      relativeTranslate,
    translatedSpokeEq, directSuffixEq] at translatedAvoid
  simpa [fallbackCenter, physicalTranslate,
    finalCoordinatedSource, finalCoordinatedPlacement,
    finalCoordinatedSourceRoutes] using translatedAvoid.symm

/-- A successful oblique direct occurrence strictly avoids a complete
translated failed-choice occurrence at every nonzero shift whose physical
target center coincides with the direct target. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_sameCenter
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
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
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
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
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_directSegment_not_axisAligned_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero centersEqual
  have spokePieceAvoid :=
    retainedFinalCoordinatedObliqueDirectOccurrencePieces_strictlyAvoid_translatedFallbackSuffix_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero centersEqual
  have directSuffixBoundaryAvoid :=
    retainedFinalCoordinatedObliqueDirectOccurrenceSuffix_strictlyAvoids_translatedFallbackBoundaryPrefix_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directOblique relativeTranslate
      relativeTranslateNonzero centersEqual
  have assembled :=
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_join_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup fallbackBoundary fallbackSuffix fallbackBoundaryPoint
      fallbackBoundaryLast fallbackSuffixHead
      (by simpa [fallbackBoundary] using prefixBoundaryAvoid)
      (by simpa [source, placement, routes, fallbackSuffix,
        physicalTranslate] using spokePieceAvoid.1)
      (by simpa [source, placement, routes, directSuffix,
        fallbackBoundary] using directSuffixBoundaryAvoid)
      (by simpa [source, placement, routes, directSuffix,
        fallbackSuffix, physicalTranslate] using spokePieceAvoid.2)
  simpa [source, placement, routes, fallbackBoundary,
    fallbackSuffix, physicalTranslate,
    retainedFinalTranslatedFallbackOccurrenceRoute] using assembled

/-- Every oblique successful direct route strictly avoids every nontrivially
translated failed-choice route, including shared physical target centers. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_strictlyAvoids_translated_of_first_choice_some_second_none_of_not_axisAligned_of_nonzero
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
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
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
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
  · exact
      retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directOblique relativeTranslate
        relativeTranslateNonzero centersEqual
  · exact
      retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_translatedFallbackOccurrenceRoute_of_distinctCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directOblique relativeTranslate
        relativeTranslateNonzero centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
