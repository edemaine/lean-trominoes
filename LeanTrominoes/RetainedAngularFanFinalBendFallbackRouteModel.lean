/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendFallbackKindSemantics
import LeanTrominoes.RetainedAngularFanFinalBendFallbackRouteTerminalModel

/-! # Indexed fallback-route model for final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- An indexed final-bend fallback is the ordinary Figure 7 splice with the
exact semantic terminal datum. -/
theorem FinalBendIndexedOccurrence.fallbackOccurrenceRoute_eq_model
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    retainedFinalFallbackOccurrenceRoute occurrence.retained
        occurrence.clause occurrence.literal occurrence.clauseIndex
          occurrence.literalIndex =
      RetainedFallbackFanKind.ordinary.splicedOwnFigure7Route
        occurrence.scaledRoute
        (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
          (bendRouteTerminalData occurrence.taggedBend.1.incomingPort
            occurrence.taggedBend.1.outgoingPort
            occurrence.localClauseIndex occurrence.literalIndex))
        occurrence.slot := by
  rw [occurrence.fallbackOccurrenceRoute_eq_terminalModel]
  rw [occurrence.fallbackKind_eq_ordinary]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
