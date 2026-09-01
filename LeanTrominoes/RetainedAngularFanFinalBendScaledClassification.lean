/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalBendTerminalDataSemantics
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-! # Scaled terminal classification of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The scaled final source route at an indexed retained bend has the exact
scaled corner-table terminal datum. -/
theorem FinalBendIndexedOccurrence.scaledRoute_classified
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    retainedTerminalDirectionClassify
        (routeTerminalVector occurrence.scaledRoute) =
      some (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor
        (bendRouteTerminalData
          occurrence.taggedBend.1.incomingPort
          occurrence.taggedBend.1.outgoingPort
          occurrence.localClauseIndex occurrence.literalIndex)) := by
  have classified := finalCoordinatedScaledSourceRoute_classified
    occurrence.retained
    (PeriodicThreeSATThree.formula_isLocal occurrence.sourceLocal)
    (PeriodicThreeSATThree.formula_widthAtMostThree occurrence.sourceWidth)
    (PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq
      occurrence.source)
    (PeriodicThreeSATThree.formula_clausesNonempty
      occurrence.source occurrence.sourceClausesNonempty)
    occurrence.clauseMember occurrence.literalMember
  dsimp only at classified
  change retainedTerminalDirectionClassify
      (routeTerminalVector occurrence.scaledRoute) =
    some (scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor
      (finalBendActualTerminalDataAt occurrence.source
        occurrence.clauseIndex occurrence.literalIndex)) at classified
  rw [finalBendTerminalData_eq occurrence.source
    occurrence.sourceLocal occurrence.sourceWidth
    occurrence.sourceClausesNonempty occurrence.positiveOffsets
    occurrence.taggedBend occurrence.clauseIndex
    occurrence.taggedBendIndexed occurrence.literalIndex] at classified
  unfold finalBendSemanticTerminalDataAt at classified
  cases h : occurrence.taggedBend.2 <;>
    simpa [FinalBendIndexedOccurrence.localClauseIndex, h] using classified

end PeriodicEightOccurrenceSplit
end LeanTrominoes
