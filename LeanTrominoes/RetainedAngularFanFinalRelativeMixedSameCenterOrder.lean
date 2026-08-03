import LeanTrominoes.RetainedAngularFanFinalRelativeMixedOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeDirectSourceSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedStrictOrder
import LeanTrominoes.RetainedAngularFanFinalMixedCenter
import LeanTrominoes.RetainedAngularFanFinalMixedOuterSelection

/-!
# Periodic same-center mixed order

If a direct occurrence center equals a nontrivially translated fallback
center, the two literals represent the same wrapped atom but different stored
occurrences.  Their existing occurrence slots therefore retain the compatible
angular order.  Relative route planarity and the common physical endpoint
force the aligned direct and fallback terminal directions to differ, upgrading
that order to the strict form used by outer-fan separation.
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

/-- A canonical center cannot coincide with a nonzero translate of the very
same stored occurrence. -/
theorem retainedFinalOccurrenceIndices_ne_of_center_eq_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
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
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    (firstClauseIndex, firstLiteralIndex) ≠
      (secondClauseIndex, secondLiteralIndex) := by
  intro occurrencesEqual
  have clauseIndexEqual : firstClauseIndex = secondClauseIndex :=
    congrArg Prod.fst occurrencesEqual
  have literalIndexEqual : firstLiteralIndex = secondLiteralIndex :=
    congrArg Prod.snd occurrencesEqual
  have taggedClausesEqual :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstClauseMember secondClauseMember clauseIndexEqual
  have clausesEqual : firstClause = secondClause :=
    congrArg Prod.fst taggedClausesEqual
  subst secondClause
  have taggedLiteralsEqual :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstLiteralMember secondLiteralMember literalIndexEqual
  have literalsEqual : firstLiteral = secondLiteral :=
    congrArg Prod.fst taggedLiteralsEqual
  subst secondLiteral
  have periodPositive :
      0 < (finalCoordinatedPlacement formula).period := by
    simpa [finalCoordinatedPlacement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  exact
    PeriodicVariablePlacement.point_ne_add_translation_of_nonzero
      (finalCoordinatedPlacement formula) periodPositive
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula)
        firstClause firstLiteral)
      relativeTranslate relativeTranslateNonzero centersEqual

/-- A same-physical-center relative mixed pair inherits compatible occurrence
slot and terminal-direction order from the stored occurrence order. -/
theorem
    retainedFinalDirectFallback_angularOrderCompatible_of_center_eq_translated
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
    RetainedDirectSourceRouteChoice.FallbackAngularOrderCompatible
      choice
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
      (retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex)
      (retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex) := by
  exact
    retainedFinalDirectFallback_angularOrderCompatible
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      (retainedFinalCanonicalLiteralPosition_eq_translated_imp_atoms_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate centersEqual)
      (retainedFinalOccurrenceIndices_ne_of_center_eq_translated_of_nonzero
        formula directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate relativeTranslateNonzero centersEqual)

/-- At a common physical center, an aligned direct source terminal and the
translated fallback terminal have different directions. -/
theorem
    retainedFinalDirectFallbackTerminalDirections_ne_of_center_eq_translated_of_directSegment_axisAligned
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
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 ≠
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1 := by
  let placement := finalCoordinatedPlacement formula
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      (placement.translation relativeTranslate) fallbackRoute
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
  let fallbackTerminal : RetainedTerminalData :=
    classifiedRetainedTerminalData (routeTerminalVector fallbackRoute)
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackLength : 2 ≤ fallbackRoute.length := by
    simpa [fallbackRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackLength :
      2 ≤ translatedFallbackRoute.length := by
    simpa [translatedFallbackRoute, translatePolyline] using fallbackLength
  have directOrthogonal : OrthogonalPolyline directRoute := by
    simpa [directRoute] using
      retainedFinalDirectSourceRoute_orthogonal_of_sourceSegment_axisAligned
        formula directClauseIndex directLiteralIndex
        choice choiceLookup directAligned
  have fallbackOrthogonal : OrthogonalPolyline fallbackRoute := by
    simpa [fallbackRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
        fallbackChoiceNone
  have translatedFallbackOrthogonal :
      OrthogonalPolyline translatedFallbackRoute :=
    fallbackOrthogonal.translate (placement.translation relativeTranslate)
  have directEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackLast :
      translatedFallbackRoute.getLast? =
        some
          (Cell.add (placement.translation relativeTranslate)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement fallbackClause fallbackLiteral)) := by
    simp [translatedFallbackRoute, translatePolyline,
      fallbackRoute, placement, fallbackEndpoints.2]
  have sameFinish :
      directRoute.getLast? = translatedFallbackRoute.getLast? := by
    rw [show directRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral) by
          simpa [directRoute, placement] using directEndpoints.2,
      translatedFallbackLast]
    apply congrArg some
    simpa [placement, Cell.add, add_comm] using centersEqual
  have rawAvoid :
      RoutesAvoidEachOther directRoute translatedFallbackRoute := by
    simpa [directRoute, fallbackRoute, translatedFallbackRoute,
      placement] using
      finalCoordinatedSourceRoutes_avoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate relativeTranslateNonzero
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) = some directTerminal := by
    simpa only [directRoute, directTerminal] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  have fallbackClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector fallbackRoute) = some fallbackTerminal := by
    simpa only [fallbackRoute, fallbackTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have translatedFallbackClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector translatedFallbackRoute) =
        some fallbackTerminal := by
    simpa [translatedFallbackRoute,
      routeTerminalVector_translatePolyline] using fallbackClassified
  rw [show
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 = directTerminal.1 from rfl]
  rw [show
    classifiedRetainedTerminalData
        (routeTerminalVector fallbackRoute) = fallbackTerminal from rfl]
  exact
    retainedTerminalDataDirections_ne_of_routesAvoidEachOther
      directTerminal fallbackTerminal
      directLength translatedFallbackLength
      directOrthogonal translatedFallbackOrthogonal
      sameFinish rawAvoid directClassified translatedFallbackClassified

/-- The periodic same-center aligned mixed pair has the strict angular order
required by positioned outer-fan separation. -/
theorem
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_axisAligned
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
    DirectFallbackStrictAngularOrderCompatible
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
      (retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex)
      (retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex) := by
  apply directFallbackStrictAngularOrderCompatible_of_compatible_of_ne
  · exact
      retainedFinalDirectFallback_angularOrderCompatible_of_center_eq_translated
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        relativeTranslate relativeTranslateNonzero centersEqual
  · exact
      retainedFinalDirectFallbackTerminalDirections_ne_of_center_eq_translated_of_directSegment_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directAligned relativeTranslate
        relativeTranslateNonzero centersEqual

/-- An oblique direct terminal and the axis-aligned fallback terminal have
different directions, so compatible same-center occurrence order is strict. -/
theorem
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_directSegment_not_axisAligned
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
    (directNotAligned : ¬choice.sourceSegment.IsAxisAligned)
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
    DirectFallbackStrictAngularOrderCompatible
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
      (retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex)
      (retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex) := by
  apply directFallbackStrictAngularOrderCompatible_of_compatible_of_ne
  · exact
      retainedFinalDirectFallback_angularOrderCompatible_of_center_eq_translated
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        relativeTranslate relativeTranslateNonzero centersEqual
  · let fallbackRoute :=
      finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex
    let fallbackTerminal : RetainedTerminalData :=
      classifiedRetainedTerminalData
        (routeTerminalVector fallbackRoute)
    have fallbackClassified :
        retainedTerminalDirectionClassify
            (Cell.sub
              (polylineLastEntrance fallbackRoute)
              (fallbackRoute.getLastD (0, 0))) =
          some fallbackTerminal := by
      simpa only [fallbackRoute, fallbackTerminal] using
        finalCoordinatedSourceRoute_finalSegment_classified
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          fallbackClauseMember fallbackLiteralMember
    have fallbackAligned :
        (GridSegment.mk
          (polylineLastEntrance fallbackRoute)
          (fallbackRoute.getLastD (0, 0))).IsAxisAligned := by
      simpa only [fallbackRoute] using
        finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          fallbackClauseMember fallbackLiteralMember fallbackChoiceNone
    rw [show
      finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex =
        fallbackRoute from rfl]
    rw [show
      classifiedRetainedTerminalData
          (routeTerminalVector fallbackRoute) =
        fallbackTerminal from rfl]
    exact
      choice.direction_ne_of_otherTerminal_aligned
        (otherStart := polylineLastEntrance fallbackRoute)
        (otherFinish := fallbackRoute.getLastD (0, 0))
        (otherTerminal := fallbackTerminal)
        fallbackClassified fallbackAligned directNotAligned

/-- Equality of translated canonical centers becomes equality of the direct
positioned fan center and the translated fallback's fully refined center. -/
theorem retainedFinalDirectTranslatedFallback_positionedFanCenters_eq_of_sameCenter
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
    (relativeTranslate : Cell)
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
    let translatedFallbackRoute :=
      translatePolyline
        ((finalCoordinatedPlacement formula).translation relativeTranslate)
        (finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex)
    retainedDirectSourcePositionedFanCenterAt
        choice.origin choice.kind choice.index =
      Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline retainedAngularFanSourceClearanceFactor
          translatedFallbackRoute).getLastD (0, 0)) := by
  dsimp only
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  have directFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember
      directLiteralMember choiceLookup
  have fallbackEndpoint :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember).2
  have fallbackLastD :
      fallbackRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral := by
    rw [List.getLastD_eq_getLast?, show
      fallbackRoute.getLast? = _ by simpa [fallbackRoute] using fallbackEndpoint]
    rfl
  have fallbackNonempty : fallbackRoute ≠ [] := by
    intro empty
    change fallbackRoute.getLast? = _ at fallbackEndpoint
    rw [empty] at fallbackEndpoint
    simp at fallbackEndpoint
  have translatedCenter :
      Cell.add sourceTranslate
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral := by
    simpa [sourceTranslate, Cell.add, add_comm] using centersEqual.symm
  rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish,
    directFinish, scalePolyline_getLastD,
    translatePolyline_getLastD sourceTranslate fallbackRoute fallbackNonempty,
    fallbackLastD, retainedAngularFanSourceClearanceFactor_eq,
    translatedCenter, Cell.scale_scale]
  norm_num

/-- Strict same-center order separates a direct route from the selected
translated ordinary-or-escaped fallback outer replacement. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_order
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (fallbackClauseIndex fallbackLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (choice : RetainedDirectSourceRouteChoice)
    (directSlot : RetainedTerminalSlot)
    (angularOrder :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      let rawTerminal :=
        classifiedRetainedTerminalData (routeTerminalVector rawRoute)
      let fallbackSlot :=
        retainedFinalCoordinatedOccurrenceSlot
          formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
      DirectFallbackStrictAngularOrderCompatible
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1
        rawTerminal.1 directSlot fallbackSlot)
    (centersEqual :
      let translatedRawRoute :=
        translatePolyline
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex)
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline retainedAngularFanSourceClearanceFactor
            translatedRawRoute).getLastD (0, 0)))
    (fallbackLengthPositive :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      0 < (classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)).2)
    (fallbackEscapeStrict :
      let rawRoute :=
        finalCoordinatedSourceRoutes
          formula fallbackClauseIndex fallbackLiteralIndex
      let rawTerminal :=
        classifiedRetainedTerminalData (routeTerminalVector rawRoute)
      retainedTerminalFanOuterSourceEscapeLength <
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor rawTerminal)) :
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute directSlot)
      (retainedFinalTranslatedFallbackOuterReplacement
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  let rawRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedRawRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      rawRoute
  let rawTerminal :=
    classifiedRetainedTerminalData (routeTerminalVector rawRoute)
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        translatedRawRoute).getLastD (0, 0))
  unfold retainedFinalTranslatedFallbackOuterReplacement
  dsimp only
  by_cases singletonPrefix : rawRoute.dropLast.length = 1
  · rw [if_pos (by simpa only [rawRoute] using singletonPrefix)]
    exact
      choice.completeRoute_strictlyAvoids_scaledEscapedFallbackAt_of_order
        directSlot rawTerminal fallbackSlot fallbackCenter
        (by simpa only [translatedRawRoute, rawRoute, fallbackCenter] using centersEqual)
        (by simpa only [rawRoute, rawTerminal, fallbackSlot] using angularOrder)
        (by simpa only [rawRoute, rawTerminal] using fallbackLengthPositive)
        (by simpa only [rawRoute, rawTerminal] using fallbackEscapeStrict)
  · rw [if_neg (by simpa only [rawRoute] using singletonPrefix)]
    exact
      choice.completeRoute_strictlyAvoids_scaledOrdinaryFallbackAt_of_order
        directSlot rawTerminal fallbackSlot fallbackCenter
        (by simpa only [translatedRawRoute, rawRoute, fallbackCenter] using centersEqual)
        (by simpa only [rawRoute, rawTerminal, fallbackSlot] using angularOrder)
        (by simpa only [rawRoute, rawTerminal] using fallbackLengthPositive)
        (Nat.zero_lt_of_lt
          (by simpa only [rawRoute, rawTerminal] using fallbackEscapeStrict))

end PeriodicOrthocrossing
end LeanTrominoes
