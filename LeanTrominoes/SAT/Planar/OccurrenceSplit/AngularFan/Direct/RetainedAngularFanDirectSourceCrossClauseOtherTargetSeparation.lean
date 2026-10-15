/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceCrossClauseCertificates

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
  intro firstClause secondClause firstIndex secondIndex firstSlot secondSlot different
  dsimp only
  intro targetDifferent rectanglesOverlap
  have checked := crossoverOtherTargetsCheck_correct firstClause
  simp only [crossoverOtherTargetsCheck, crossLocalChoicesCheck, finiteAll_eq_true,
    guardedCheck_eq_true] at checked
  exact crossPiecesCheck_sound _ _ firstSlot secondSlot
    (checked secondClause different firstIndex secondIndex targetDifferent rectanglesOverlap firstSlot secondSlot)

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
  intro firstArm secondArm firstClause secondClause firstIndex secondIndex firstSlot secondSlot different
  dsimp only
  intro targetDifferent rectanglesOverlap
  have checked := duplicatorOtherTargetsCheck_correct firstArm firstClause
  simp only [duplicatorOtherTargetsCheck, crossLocalChoicesCheck, finiteAll_eq_true,
    guardedCheck_eq_true] at checked
  exact crossPiecesCheck_sound _ _ firstSlot secondSlot
    (checked secondArm secondClause different firstIndex secondIndex targetDifferent rectanglesOverlap firstSlot secondSlot)

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
