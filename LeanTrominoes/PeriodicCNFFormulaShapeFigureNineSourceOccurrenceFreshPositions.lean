/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceSubdivisionPositions
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedAtoms

/-! # Actual fresh polarity variable positions selected by source descriptors -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open FormulaShapeFigureNinePolarityRouteTail PeriodicOrthocrossing
open PeriodicCNFStripReduction.HorizontalRoutedRouteHeader
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

local instance occurrenceFreshPositionVariableDecidableEq {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Decoding either occurrence of a fresh variable recovers its exact
source indices and hence its first affine subdivision point. -/
theorem OccurrenceWitness.freshPolarityPosition
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal) (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (fresh : occurrence.header.polarity.operation = .incompatible ∨
      occurrence.header.polarity.operation = .complementFresh)
    (atom : PolarityNormalizedVariable
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (decoded : (sourceIndexedDescriptorOf occurrence.generatedClauseIndex occurrence.header.polarity.indexed).atom?
      (refinedSource
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source)).erase = some atom) :
    (placement
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty)).position atom =
      Cell.add (Cell.scale 3 witness.metadata.clause.position) (sourceFirstDirection occurrence.header).step := by
  obtain ⟨refinedClause, clauseLookup, decodedLiteral⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨refinedLiteral, literalLookup, atomEq⟩ := Option.map_eq_some_iff.mp decodedLiteral
  have freshAtom : atom = .inr
      ((occurrence.generatedClauseIndex, occurrence.header.polarity.indexed.sourceLiteralIndex), refinedLiteral) := by
    rcases fresh with fresh | fresh <;>
      simpa only [sourceIndexedDescriptorOf, ClauseProfilePolarityRouteOperation.Descriptor.indexed, fresh] using atomEq.symm
  obtain ⟨sourceClause, sourceLiteral, clauseMember, literalMember, _⟩ :=
    exists_sourceLiteral_of_refinedSource_lookup _ _ clauseLookup literalLookup
  rw [freshAtom, placement_fresh_position]
  exact (witness.polaritySubdivisionPositions sourceLocal sourceWidth sourceOccurrences sourceNonempty
    sourceClause clauseMember sourceLiteral literalMember).1

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
