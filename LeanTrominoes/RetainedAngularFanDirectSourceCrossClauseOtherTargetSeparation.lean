/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceCycleSeparation

/-!
# Cross-clause direct routes with different target centers

The same-clause direct atlas already separates the incidences leaving one
clause gate.  For different clauses in one physical component, most route
pairs are separated immediately by their conservative radius-288 source
segment rectangles.  The finitely many overlapping rectangles with different
target endpoints admit a small collection of linear envelope certificates.

This file packages both cases for crossover and duplicator components.  The
remaining same-target case deliberately stays separate: its occurrence slots
are constrained by angular order and are not independent finite parameters.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- The direct choice at the origin determined by one local atlas entry. -/
def retainedDirectSourceLocalChoice
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    RetainedDirectSourceRouteChoice :=
  ⟨(0, 0), kind, index⟩

@[simp]
theorem retainedDirectSourceFanPositioningOffset_zero :
    retainedDirectSourceFanPositioningOffset (0, 0) = (0, 0) := by
  simp [retainedDirectSourceFanPositioningOffset, Cell.scale]

@[simp]
theorem retainedDirectSourceFanCompleteRouteAt_getLast?
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    (retainedDirectSourceFanCompleteRouteAt kind index slot).getLast? =
      some
        (Cell.add
          (retainedDirectSourceFanCenterAt kind index)
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val))) := by
  unfold retainedDirectSourceFanCompleteRouteAt
  exact
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_getLast?
      (retainedDirectSourceFanCenterAt kind index)
      (retainedDirectSourceFanTerminalAt kind index)
      slot
      (retainedDirectSourceFanEscapeAt kind index slot)
      (retainedDirectSourceFanTerminalAt_length_positive kind index)
      (retainedDirectSourceFanTerminalAt_escape_fits kind index)

/-- Conservative fully refined route rectangles for two local choices are
strictly separated. -/
def RetainedDirectSourceRouteChoice.SourceRectanglesSeparated
    (first second : RetainedDirectSourceRouteChoice) : Prop :=
  ClosedGridRectanglesSeparated
    (coordinateRadiusLower 288
      (Cell.scale
        (retainedTerminalFanTotalRefinement * 4)
        first.sourceSegment.coordinateLower))
    (coordinateRadiusUpper 288
      (Cell.scale
        (retainedTerminalFanTotalRefinement * 4)
        first.sourceSegment.coordinateUpper))
    (coordinateRadiusLower 288
      (Cell.scale
        (retainedTerminalFanTotalRefinement * 4)
        second.sourceSegment.coordinateLower))
    (coordinateRadiusUpper 288
      (Cell.scale
        (retainedTerminalFanTotalRefinement * 4)
        second.sourceSegment.coordinateUpper))

instance
    (first second : RetainedDirectSourceRouteChoice) :
    Decidable (first.SourceRectanglesSeparated second) := by
  unfold RetainedDirectSourceRouteChoice.SourceRectanglesSeparated
  infer_instance

/-- Separated source rectangles give strict separation of the complete
Figure 7 routes they contain. -/
theorem
    RetainedDirectSourceRouteChoice.completeFigure7Routes_strictlyAvoid_of_sourceRectanglesSeparated
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (separated : first.SourceRectanglesSeparated second) :
    RoutesStrictlyAvoidEachOther
      (first.completeFigure7Route firstSlot)
      (second.completeFigure7Route secondSlot) := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
  · intro point pointMember
    exact
      first.completeFigure7Route_point_in_sourceSegmentRectangle
        firstSlot pointMember
  · intro point pointMember
    exact
      second.completeFigure7Route_point_in_sourceSegmentRectangle
        secondSlot pointMember
  · exact separated

/-- Primitive inward direction selected by a local direct choice. -/
def retainedDirectSourceCrossClausePrimitive
    (choice : RetainedDirectSourceRouteChoice) : Cell :=
  (retainedTerminalFanOuterInwardRayOfLength
    (retainedDirectSourcePrefixChoiceAt
      choice.kind choice.index).direction 1).vector

/-- A separator normal biased between the two selected inward directions. -/
def retainedDirectSourceCrossClauseNormalWithWeight
    (first second : RetainedDirectSourceRouteChoice)
    (weight : Nat) : Cell :=
  let firstDirection :=
    (retainedDirectSourcePrefixChoiceAt
      first.kind first.index).direction
  let secondDirection :=
    (retainedDirectSourcePrefixChoiceAt
      second.kind second.index).direction
  let earlier :=
    if firstDirection.angularRank < secondDirection.angularRank then
      retainedDirectSourceCrossClausePrimitive first
    else
      retainedDirectSourceCrossClausePrimitive second
  let later :=
    if firstDirection.angularRank < secondDirection.angularRank then
      retainedDirectSourceCrossClausePrimitive second
    else
      retainedDirectSourceCrossClausePrimitive first
  if Cell.add earlier later = (0, 0) then
    earlier
  else
    rotateCellQuarterTurn
      (Cell.add (Cell.scale weight earlier) later)

/-- The four envelope normals used by the finite cross-clause certificate. -/
def retainedDirectSourceCrossClauseCandidateNormals
    (first second : RetainedDirectSourceRouteChoice) : List Cell :=
  [retainedDirectSourceCrossClauseNormalWithWeight first second 1,
    retainedDirectSourceCrossClauseNormalWithWeight first second 8,
    retainedDirectSourceCrossClauseNormalWithWeight first second 0,
    rotateCellQuarterTurn
      (if
        (retainedDirectSourcePrefixChoiceAt
          first.kind first.index).direction.angularRank <
        (retainedDirectSourcePrefixChoiceAt
          second.kind second.index).direction.angularRank
      then retainedDirectSourceCrossClausePrimitive first
      else retainedDirectSourceCrossClausePrimitive second)]

/-- Seven linear envelope checks suffice to assemble two complete local
Figure 7 routes: the four pairs in the escape/tail decomposition, followed
by the two outer-route/spoke crosses and the spoke pair. -/
def RetainedDirectSourceRouteChoice.CrossClausePiecesLinearlySeparated
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot) : Prop :=
  let normals :=
    retainedDirectSourceCrossClauseCandidateNormals first second
  RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFanEscapeAt first.kind
        first.index firstSlot).route
      (retainedDirectSourceFanEscapeAt second.kind
        second.index secondSlot).route ∧
    RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFanEscapeAt first.kind
        first.index firstSlot).route
      (retainedDirectSourceFanCompleteTailAt second.kind
        second.index secondSlot) ∧
    RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFanCompleteTailAt first.kind
        first.index firstSlot)
      (retainedDirectSourceFanEscapeAt second.kind
        second.index secondSlot).route ∧
    RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFanCompleteTailAt first.kind
        first.index firstSlot)
      (retainedDirectSourceFanCompleteTailAt second.kind
        second.index secondSlot) ∧
    RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFanCompleteRouteAt
        first.kind first.index firstSlot)
      (retainedDirectSourceFigure7SpokeAt
        second.kind second.index secondSlot) ∧
    RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFigure7SpokeAt
        first.kind first.index firstSlot)
      (retainedDirectSourceFanCompleteRouteAt
        second.kind second.index secondSlot) ∧
    RoutesLinearlySeparatedBySome normals
      (retainedDirectSourceFigure7SpokeAt
        first.kind first.index firstSlot)
      (retainedDirectSourceFigure7SpokeAt
        second.kind second.index secondSlot)

instance
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot) :
    Decidable
      (first.CrossClausePiecesLinearlySeparated
        second firstSlot secondSlot) := by
  unfold
    RetainedDirectSourceRouteChoice.CrossClausePiecesLinearlySeparated
  infer_instance

/-- The seven envelope checks assemble into strict separation of the two
complete local Figure 7 routes. -/
theorem
    retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_crossClausePieces
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex :
      Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex :
      Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (pieces :
      (retainedDirectSourceLocalChoice firstKind firstIndex)
        |>.CrossClausePiecesLinearlySeparated
          (retainedDirectSourceLocalChoice secondKind secondIndex)
          firstSlot secondSlot) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice firstKind firstIndex)
        |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice secondKind secondIndex)
        |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice firstKind firstIndex
  let second :=
    retainedDirectSourceLocalChoice secondKind secondIndex
  let normals :=
    retainedDirectSourceCrossClauseCandidateNormals first second
  change first.CrossClausePiecesLinearlySeparated
      second firstSlot secondSlot at pieces
  dsimp only [
    RetainedDirectSourceRouteChoice.CrossClausePiecesLinearlySeparated]
    at pieces
  have escapeEscape :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.1
  have escapeTail :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.2.1
  have tailEscape :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.2.2.1
  have tailTail :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.2.2.2.1
  have completeSpoke :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.2.2.2.2.1
  have spokeComplete :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.2.2.2.2.2.1
  have spokeSpoke :=
    routesStrictlyAvoidEachOther_of_linearlySeparatedBySome
      normals _ _ pieces.2.2.2.2.2.2
  have firstEscapeAvoidSecondComplete :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanEscapeAt
          firstKind firstIndex firstSlot).route
        (retainedDirectSourceFanCompleteRouteAt
          secondKind secondIndex secondSlot) := by
    rw [retainedDirectSourceFanCompleteRouteAt,
      retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
    exact escapeEscape.join_right escapeTail
      (retainedDirectSourceFanEscapeAt
        secondKind secondIndex secondSlot).last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        (retainedDirectSourceFanCenterAt secondKind secondIndex)
        (retainedDirectSourceFanTerminalAt secondKind secondIndex)
        secondSlot)
  have firstTailAvoidSecondComplete :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteTailAt
          firstKind firstIndex firstSlot)
        (retainedDirectSourceFanCompleteRouteAt
          secondKind secondIndex secondSlot) := by
    rw [retainedDirectSourceFanCompleteRouteAt,
      retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
    exact tailEscape.join_right tailTail
      (retainedDirectSourceFanEscapeAt
        secondKind secondIndex secondSlot).last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        (retainedDirectSourceFanCenterAt secondKind secondIndex)
        (retainedDirectSourceFanTerminalAt secondKind secondIndex)
        secondSlot)
  have completeComplete :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          firstKind firstIndex firstSlot)
        (retainedDirectSourceFanCompleteRouteAt
          secondKind secondIndex secondSlot) := by
    rw [retainedDirectSourceFanCompleteRouteAt,
      retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail]
    exact firstEscapeAvoidSecondComplete.join_left
      firstTailAvoidSecondComplete
      (retainedDirectSourceFanEscapeAt
        firstKind firstIndex firstSlot).last_eq
      (retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        (retainedDirectSourceFanCenterAt firstKind firstIndex)
        (retainedDirectSourceFanTerminalAt firstKind firstIndex)
        firstSlot)
  have firstCompleteAvoidSecondFigure7 :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFanCompleteRouteAt
          firstKind firstIndex firstSlot)
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            secondKind secondIndex secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            secondKind secondIndex secondSlot)) := by
    exact completeComplete.join_right completeSpoke
      (retainedDirectSourceFanCompleteRouteAt_getLast?
        secondKind secondIndex secondSlot)
      (retainedDirectSourceFigure7SpokeAt_head?
        secondKind secondIndex secondSlot)
  have firstSpokeAvoidSecondFigure7 :
      RoutesStrictlyAvoidEachOther
        (retainedDirectSourceFigure7SpokeAt
          firstKind firstIndex firstSlot)
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            secondKind secondIndex secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            secondKind secondIndex secondSlot)) := by
    exact spokeComplete.join_right spokeSpoke
      (retainedDirectSourceFanCompleteRouteAt_getLast?
        secondKind secondIndex secondSlot)
      (retainedDirectSourceFigure7SpokeAt_head?
        secondKind secondIndex secondSlot)
  have raw :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            firstKind firstIndex firstSlot)
          (retainedDirectSourceFigure7SpokeAt
            firstKind firstIndex firstSlot))
        (joinAtEndpoint
          (retainedDirectSourceFanCompleteRouteAt
            secondKind secondIndex secondSlot)
          (retainedDirectSourceFigure7SpokeAt
            secondKind secondIndex secondSlot)) :=
    firstCompleteAvoidSecondFigure7.join_left
      firstSpokeAvoidSecondFigure7
      (retainedDirectSourceFanCompleteRouteAt_getLast?
        firstKind firstIndex firstSlot)
      (retainedDirectSourceFigure7SpokeAt_head?
        firstKind firstIndex firstSlot)
  simpa [RetainedDirectSourceRouteChoice.completeFigure7Route,
    RetainedDirectSourceRouteChoice.completeRoute,
    RetainedDirectSourceRouteChoice.figure7Spoke,
    retainedDirectSourcePositionedFanCompleteRouteAt,
    retainedDirectSourceLocalChoice] using raw

/-- Every exceptional pair of different crossover clauses with different
target endpoints has the seven linear envelope certificates. -/
theorem
    retainedDirectSourceCrossoverCrossClauseOtherTarget_piecesLinearlySeparated :
    ∀ (firstClauseIndex secondClauseIndex : Fin 26)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover secondClauseIndex)).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstClauseIndex ≠ secondClauseIndex →
      let first :=
        retainedDirectSourceLocalChoice
          (.crossover firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.crossover secondClauseIndex) secondIndex
      first.sourceSegment.finish ≠ second.sourceSegment.finish →
      ¬first.SourceRectanglesSeparated second →
        first.CrossClausePiecesLinearlySeparated
          second firstSlot secondSlot := by
  native_decide

/-- Every exceptional pair of different duplicator clauses with different
target endpoints has the seven linear envelope certificates. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseOtherTarget_piecesLinearlySeparated :
    ∀ (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
      (firstClauseIndex secondClauseIndex : Fin 2)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator firstArm firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator secondArm secondClauseIndex)).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      (firstArm, firstClauseIndex) ≠
          (secondArm, secondClauseIndex) →
      let first :=
        retainedDirectSourceLocalChoice
          (.duplicator firstArm firstClauseIndex) firstIndex
      let second :=
        retainedDirectSourceLocalChoice
          (.duplicator secondArm secondClauseIndex) secondIndex
      first.sourceSegment.finish ≠ second.sourceSegment.finish →
      ¬first.SourceRectanglesSeparated second →
        first.CrossClausePiecesLinearlySeparated
          second firstSlot secondSlot := by
  native_decide

/-- Translating an origin translates the assembled complete Figure 7 route
by the common fully refined physical offset. -/
theorem
    RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route
    (choice : RetainedDirectSourceRouteChoice)
    (offset : Cell)
    (slot : RetainedTerminalSlot) :
    (choice.translateOrigin offset).completeFigure7Route slot =
      translatePolyline
        (retainedDirectSourceFanPositioningOffset offset)
        (choice.completeFigure7Route slot) := by
  unfold RetainedDirectSourceRouteChoice.completeFigure7Route
  rw [
    RetainedDirectSourceRouteChoice.translateOrigin_completeRoute,
    RetainedDirectSourceRouteChoice.translateOrigin_figure7Spoke,
    translatePolyline_joinAtEndpoint]

/-- The finite local certificate transports to two choices with one common
component origin. -/
theorem
    retainedDirectSourceSameOriginCompleteFigure7Routes_strictlyAvoid_of_local
    (origin : Cell)
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex :
      Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex :
      Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (localAvoid :
      RoutesStrictlyAvoidEachOther
        ((retainedDirectSourceLocalChoice firstKind firstIndex)
          |>.completeFigure7Route firstSlot)
        ((retainedDirectSourceLocalChoice secondKind secondIndex)
          |>.completeFigure7Route secondSlot)) :
    RoutesStrictlyAvoidEachOther
      ((⟨origin, firstKind, firstIndex⟩ :
          RetainedDirectSourceRouteChoice)
        |>.completeFigure7Route firstSlot)
      ((⟨origin, secondKind, secondIndex⟩ :
          RetainedDirectSourceRouteChoice)
        |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice firstKind firstIndex
  let second :=
    retainedDirectSourceLocalChoice secondKind secondIndex
  have firstEq :
      (⟨origin, firstKind, firstIndex⟩ :
          RetainedDirectSourceRouteChoice) =
        first.translateOrigin origin := by
    simp [first, retainedDirectSourceLocalChoice,
      RetainedDirectSourceRouteChoice.translateOrigin, Cell.add]
  have secondEq :
      (⟨origin, secondKind, secondIndex⟩ :
          RetainedDirectSourceRouteChoice) =
        second.translateOrigin origin := by
    simp [second, retainedDirectSourceLocalChoice,
      RetainedDirectSourceRouteChoice.translateOrigin, Cell.add]
  rw [firstEq, secondEq,
    RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route,
    RetainedDirectSourceRouteChoice.translateOrigin_completeFigure7Route]
  exact localAvoid.map_add
    (retainedDirectSourceFanPositioningOffset origin)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
