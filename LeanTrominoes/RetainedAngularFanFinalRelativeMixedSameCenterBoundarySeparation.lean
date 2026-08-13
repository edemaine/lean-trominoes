/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterOrder
import LeanTrominoes.RetainedAngularFanFinalRelativeTranslatedFallbackBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeRoutedClausePrefixSeparation

/-!
# Periodic same-center mixed boundary separation

At a nonzero period shift, a successful aligned direct route can share its
physical target with a translated failed-choice route.  The translated source
corridor separates the retained prefix, while strict occurrence order at the
common fan center separates the selected outer replacement.  The translated
fallback-boundary assembly then combines the two certificates.
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

/-- An aligned successful direct boundary strictly avoids a translated
failed-choice boundary at a nonzero shift even when their physical target
centers coincide. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_axisAligned_of_sameCenter
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
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula directLiteral directClauseIndex directLiteralIndex))
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let translatedRawRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
  have kindNe : choice.kind ≠ .routedClause := by
    intro kindEq
    exact
      (choice.sourceSegment_not_axisAligned_of_kind_eq_routedClause
        kindEq) directAligned
  have corridor :=
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_directSegment_axisAligned_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero
  apply
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone relativeTranslate
      (choice.completeRoute directSlot)
  · have prefixAvoid :=
      retainedFinalSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_corridorSeparated
        formula translatedRawRoute
        directClauseIndex directLiteralIndex choice directSlot
        choiceLookup kindNe corridor
    dsimp only
    rw [scalePolyline_dropLast_eq,
      scalePolyline_dropLast_eq,
      scalePolyline_scalePolyline_nat]
    simpa only [directSlot, translatedRawRoute,
      retainedAngularFanSourceClearanceFactor,
      Nat.cast_ofNat] using prefixAvoid.symm
  · exact
      RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_order
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate choice directSlot
        (retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_axisAligned
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember choiceLookup
          fallbackChoiceNone directAligned relativeTranslate
          relativeTranslateNonzero centersEqual)
        (retainedFinalDirectTranslatedFallback_positionedFanCenters_eq_of_sameCenter
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember choiceLookup
          relativeTranslate centersEqual)
        (finalCoordinatedSourceRoute_terminal_length_positive
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty fallbackClauseMember fallbackLiteralMember)
        (finalCoordinatedScaledSourceRoute_escapeStrict
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty fallbackClauseMember fallbackLiteralMember)

/-- An oblique successful direct boundary strictly avoids a translated
failed-choice boundary at a nonzero shift when their physical target centers
coincide. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_directSegment_not_axisAligned_of_sameCenter
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
    RoutesStrictlyAvoidEachOther
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula directLiteral directClauseIndex directLiteralIndex))
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let translatedRawRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
  apply
    strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
      fallbackChoiceNone relativeTranslate
      (choice.completeRoute directSlot)
  · have prefixAvoid :=
      retainedFinalTranslatedFallbackSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directSlot relativeTranslate
        relativeTranslateNonzero
    dsimp only
    rw [scalePolyline_dropLast_eq,
      scalePolyline_dropLast_eq,
      scalePolyline_scalePolyline_nat]
    simpa only [directSlot, translatedRawRoute,
      retainedAngularFanSourceClearanceFactor,
      Nat.cast_ofNat] using prefixAvoid.symm
  · exact
      RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackOuterReplacement_of_order
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate choice directSlot
        (retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_directSegment_not_axisAligned
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember choiceLookup
          fallbackChoiceNone directNotAligned relativeTranslate
          relativeTranslateNonzero centersEqual)
        (retainedFinalDirectTranslatedFallback_positionedFanCenters_eq_of_sameCenter
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember choiceLookup
          relativeTranslate centersEqual)
        (finalCoordinatedSourceRoute_terminal_length_positive
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty fallbackClauseMember fallbackLiteralMember)
        (finalCoordinatedScaledSourceRoute_escapeStrict
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty fallbackClauseMember fallbackLiteralMember)

/-- Every successful direct boundary strictly avoids a translated failed-choice
boundary at a nonzero shift when their physical target centers coincide. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_sameCenter
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
      (choice.completeRoute
        (retainedFinalCoordinatedOccurrenceSlot
          formula directLiteral directClauseIndex directLiteralIndex))
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
        relativeTranslate) := by
  by_cases directAligned : choice.sourceSegment.IsAxisAligned
  · exact
      RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_axisAligned_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directAligned relativeTranslate
        relativeTranslateNonzero centersEqual
  · exact
      RetainedDirectSourceRouteChoice.completeRoute_strictlyAvoids_retainedFinalTranslatedFallbackBoundaryPrefix_of_directSegment_not_axisAligned_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone directAligned relativeTranslate
        relativeTranslateNonzero centersEqual

end PeriodicOrthocrossing
end LeanTrominoes
