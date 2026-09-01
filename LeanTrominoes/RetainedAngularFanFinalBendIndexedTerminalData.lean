/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalBendTerminalDataSemantics

/-! # Exact terminal data of indexed final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The classified terminal datum of an indexed final bend is its local
corner-table datum. -/
theorem FinalBendIndexedOccurrence.rawTerminalData_eq
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes occurrence.retained
            occurrence.clauseIndex occurrence.literalIndex)) =
      bendRouteTerminalData occurrence.taggedBend.1.incomingPort
        occurrence.taggedBend.1.outgoingPort
        occurrence.localClauseIndex occurrence.literalIndex := by
  change finalBendActualTerminalDataAt occurrence.source
      occurrence.clauseIndex occurrence.literalIndex = _
  have terminalEq := finalBendTerminalData_eq occurrence.source
    occurrence.sourceLocal occurrence.sourceWidth
    occurrence.sourceClausesNonempty occurrence.positiveOffsets
    occurrence.taggedBend occurrence.clauseIndex
    occurrence.taggedBendIndexed occurrence.literalIndex
  unfold finalBendSemanticTerminalDataAt at terminalEq
  cases h : occurrence.taggedBend.2 <;>
    simpa [FinalBendIndexedOccurrence.localClauseIndex, h] using terminalEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
