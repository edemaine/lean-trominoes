/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedTerminalData
import LeanTrominoes.RetainedAngularFanFinalFallbackFigure7Identification

/-! # Indexed fallback-route terminal model for final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- An indexed final-bend fallback uses the exact semantic bend terminal;
its independent singleton-prefix policy is left explicit. -/
theorem FinalBendIndexedOccurrence.fallbackOccurrenceRoute_eq_terminalModel
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    retainedFinalFallbackOccurrenceRoute occurrence.retained
        occurrence.clause occurrence.literal occurrence.clauseIndex
          occurrence.literalIndex =
      (if (finalCoordinatedSourceRoutes occurrence.retained
            occurrence.clauseIndex occurrence.literalIndex).dropLast.length = 1
        then RetainedFallbackFanKind.escaped
        else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
        occurrence.scaledRoute
        (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (bendRouteTerminalData occurrence.taggedBend.1.incomingPort
            occurrence.taggedBend.1.outgoingPort
            occurrence.localClauseIndex occurrence.literalIndex))
        occurrence.slot := by
  have retainedLocal :=
    PeriodicThreeSATThree.formula_isLocal occurrence.sourceLocal
  have retainedWidth :=
    PeriodicThreeSATThree.formula_widthAtMostThree occurrence.sourceWidth
  have retainedOccurrences :=
    PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq
      occurrence.source
  have retainedClausesNonempty :
      ∀ retainedClause ∈ occurrence.retained.clauses,
        retainedClause ≠ [] :=
    PeriodicThreeSATThree.formula_clausesNonempty occurrence.source
      occurrence.sourceClausesNonempty
  have routeModel :=
    retainedFinalFallbackOccurrenceRoute_eq_kind_splicedOwnFigure7Route
      occurrence.retained retainedLocal retainedWidth retainedOccurrences
      retainedClausesNonempty occurrence.clauseMember
      occurrence.literalMember
  rw [routeModel]
  exact congrArg
    (fun terminal =>
      (if (finalCoordinatedSourceRoutes occurrence.retained
              occurrence.clauseIndex occurrence.literalIndex).dropLast.length = 1
          then RetainedFallbackFanKind.escaped
          else RetainedFallbackFanKind.ordinary).splicedOwnFigure7Route
        occurrence.scaledRoute
        (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          terminal)
        occurrence.slot)
    occurrence.rawTerminalData_eq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
