/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLocalRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexBounds

/-! # Gauged clause origins retain the occurrence witness's raw position -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open FormulaShapeFigureNinePolarityRouteTail PeriodicOrthocrossing

local instance occurrenceClausePositionVariableDecidableEq {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The final clockwise ordering and variable gauge preserve the raw stored
clause position as the canonical origin at this exact generated index. -/
theorem OccurrenceWitness.finalGaugedClausePosition {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal) (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (member : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx) :
    PositionedPeriodicCNF.canonicalClausePosition
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source) clause =
        witness.metadata.clause.position := by
  obtain ⟨rawClause, rawMember, positionEq⟩ :=
    retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_eq_rawPosition
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty member
  have rawClauseEq : rawClause = witness.metadata.clause :=
    Option.some.inj ((List.mk_mem_zipIdx_iff_getElem?.mp rawMember).symm.trans
      (List.mk_mem_zipIdx_iff_getElem?.mp witness.rawClauseMember))
  simpa only [rawClauseEq] using positionEq

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
