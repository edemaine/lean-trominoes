/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRoutePointAffine
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedSourceFirstDirection
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceClausePositions
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedPresentation

/-! # Polarity subdivision positions at coherent Figure 9 incidences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open FormulaShapeFigureNinePolarityRouteTail PeriodicOrthocrossing Gadget
open PeriodicCNFStripReduction.HorizontalRoutedRouteHeader
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

local instance occurrenceSubdivisionVariableDecidableEq {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- The actual polarity route selectors have affine coordinates determined
by this occurrence's own stored clause origin and finite first direction. -/
theorem OccurrenceWitness.polaritySubdivisionPositions
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal) (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (clauseMember : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx)
    (literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (literalMember : (literal, occurrence.header.polarity.indexed.sourceLiteralIndex) ∈ clause.literals.zipIdx) :
    let points := refinedRoute
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
      occurrence.generatedClauseIndex occurrence.header.polarity.indexed.sourceLiteralIndex
    points.getD 1 (0, 0) = Cell.add (Cell.scale 3 witness.metadata.clause.position)
        (sourceFirstDirection occurrence.header).step ∧
      points.getD 2 (0, 0) = Cell.add (Cell.scale 3 witness.metadata.clause.position)
        (Cell.scale 2 (sourceFirstDirection occurrence.header).step) := by
  let family := (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation
    source sourceLocal sourceWidth sourceOccurrences sourceNonempty).canonicalOrthogonalRoutes
  have endpoints := family.endpoints clause occurrence.generatedClauseIndex clauseMember
    literal occurrence.header.polarity.indexed.sourceLiteralIndex literalMember
  have orthogonal := family.orthogonal clause occurrence.generatedClauseIndex clauseMember
    literal occurrence.header.polarity.indexed.sourceLiteralIndex literalMember
  have head := endpoints.1
  rw [witness.finalGaugedClausePosition sourceLocal sourceWidth sourceOccurrences sourceNonempty clause clauseMember] at head
  dsimp only [family, PositionedPeriodicCNF.PlanarIncidencePresentation.canonicalOrthogonalRoutes,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlanarIncidencePresentation] at head orthogonal
  refine refinedRoute_initial_positions
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
    occurrence.generatedClauseIndex occurrence.header.polarity.indexed.sourceLiteralIndex
    witness.metadata.clause.position (sourceFirstDirection occurrence.header) head orthogonal ?_
  rw [← witness.sourceDirectionWord sourceLocal sourceWidth sourceOccurrences sourceNonempty]
  exact sourceBlock_directions_head occurrence.pair.1 occurrence.pair.2

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
