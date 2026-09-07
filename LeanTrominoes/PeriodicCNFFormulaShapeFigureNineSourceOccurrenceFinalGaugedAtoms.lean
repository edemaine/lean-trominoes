/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLiteralAtoms
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedRoutes
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSourceIndexedAtoms

/-! # Actual atoms at final gauged Figure 9 occurrence indices -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

local instance occurrenceFinalAtomVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  nestedVariableDecidableEq

/-- The final clockwise literal slot selects the instantiated atom carried
by the same occurrence's raw Figure 9 header. -/
theorem OccurrenceWitness.finalClockwiseLiteralAtom
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (clauseMember : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx)
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (literalMember : (literal, occurrence.header.polarity.indexed.sourceLiteralIndex) ∈
      clause.literals.zipIdx) :
    let query := occurrence.header.figurePrefix.localQuery
    instantiatedVariableMap witness.metadata.sourceClauseIndex
        witness.metadata.figureNineClauseStart witness.metadata.sourceClause
        ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 =
      literal.atom := by
  obtain ⟨rawClause, rawLiteral, rawIndex, rawMember, rawLiteralMember,
      indexEq, literalEq, _⟩ :=
    exists_composedRawLiteral_finalGauged_directionWord_exactSourceIndex
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty
      clauseMember literalMember
  have rawClauseEq : rawClause = witness.metadata.clause :=
    Option.some.inj ((List.mk_mem_zipIdx_iff_getElem?.mp rawMember).symm.trans
      (List.mk_mem_zipIdx_iff_getElem?.mp witness.rawClauseMember))
  subst rawClause
  obtain ⟨_, rawIndexEq, _⟩ := witness.rawLiteralCoordinates sourceWidth sourceNonempty
  have rawIndexEq' : rawIndex = (headerTemplateCoordinate occurrence.header).literalIndex :=
    indexEq.trans rawIndexEq.symm
  rw [rawIndexEq'] at rawLiteralMember
  rw [literalEq]
  exact witness.literalAtom sourceWidth sourceNonempty rawLiteralMember

/-- The final variable gauge changes offsets while preserving the atom at
the occurrence's exact final clause and literal indices. -/
theorem OccurrenceWitness.finalGaugedLiteralAtom
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (clauseMember : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx)
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (literalMember : (literal, occurrence.header.polarity.indexed.sourceLiteralIndex) ∈
      clause.literals.zipIdx) :
    let query := occurrence.header.figurePrefix.localQuery
    instantiatedVariableMap witness.metadata.sourceClauseIndex
        witness.metadata.figureNineClauseStart witness.metadata.sourceClause
        ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 =
      literal.atom := by
  obtain ⟨orderedClause, orderedMember, clauseEq⟩ :=
    PositionedPeriodicCNF.exists_sourceClause_of_variableGaugeClause_mem
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source)
      clauseMember
  have literalLookup := List.mk_mem_zipIdx_iff_getElem?.mp literalMember
  rw [clauseEq, PeriodicClause.variableGauge, List.getElem?_map] at literalLookup
  obtain ⟨orderedLiteral, orderedLookup, literalEq⟩ := Option.map_eq_some_iff.mp literalLookup
  have atomEq := witness.finalClockwiseLiteralAtom
    sourceLocal sourceWidth sourceOccurrences sourceNonempty orderedMember
    (List.mk_mem_zipIdx_iff_getElem?.mpr orderedLookup)
  have literalAtomEq := congrArg PeriodicLiteral.atom literalEq
  exact atomEq.trans literalAtomEq

private theorem exists_sourceLiteral_of_refinedSource_lookup
    {Variable : Type} (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    {clauseIndex literalIndex : Nat} {clause : PeriodicClause Variable}
    (clauseLookup :
      (PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinedSource
        source placement).erase.clauses[clauseIndex]? = some clause)
    {literal : PeriodicLiteral Variable}
    (literalLookup : clause[literalIndex]? = some literal) :
    ∃ sourceClause sourceLiteral,
      (sourceClause, clauseIndex) ∈ source.clauses.zipIdx ∧
      (sourceLiteral, literalIndex) ∈ sourceClause.literals.zipIdx ∧
      sourceLiteral.atom = literal.atom := by
  rw [PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinedSource,
    PositionedPeriodicCNF.erase_scale, PositionedPeriodicCNF.erase_anchorNormalize] at clauseLookup
  simp only [PeriodicCNF.anchorNormalize, PositionedPeriodicCNF.erase, List.map_map,
    List.getElem?_map, Function.comp_def] at clauseLookup
  obtain ⟨sourceClause, sourceClauseLookup, clauseEq⟩ := Option.map_eq_some_iff.mp clauseLookup
  rw [← clauseEq, PeriodicClause.anchorNormalize, List.getElem?_map] at literalLookup
  obtain ⟨sourceLiteral, sourceLiteralLookup, literalEq⟩ := Option.map_eq_some_iff.mp literalLookup
  have literalAtomEq := congrArg PeriodicLiteral.atom literalEq
  exact ⟨sourceClause, sourceLiteral,
    List.mk_mem_zipIdx_iff_getElem?.mpr sourceClauseLookup,
    List.mk_mem_zipIdx_iff_getElem?.mpr sourceLiteralLookup, literalAtomEq⟩

/-- Anchor normalization and physical refinement preserve the original atom
selected at the coherent occurrence's final source coordinates. -/
theorem OccurrenceWitness.refinedFinalGaugedLiteralAtom
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause : PeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (clauseLookup :
      (PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinedSource
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source)).erase.clauses[
          occurrence.generatedClauseIndex]? = some clause)
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (literalLookup : clause[occurrence.header.polarity.indexed.sourceLiteralIndex]? = some literal) :
    let query := occurrence.header.figurePrefix.localQuery
    instantiatedVariableMap witness.metadata.sourceClauseIndex
        witness.metadata.figureNineClauseStart witness.metadata.sourceClause
        ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 =
      literal.atom := by
  obtain ⟨sourceClause, sourceLiteral, clauseMember, literalMember, atomEq⟩ :=
    exists_sourceLiteral_of_refinedSource_lookup _ _ clauseLookup literalLookup
  exact (witness.finalGaugedLiteralAtom sourceLocal sourceWidth sourceOccurrences
    sourceNonempty clauseMember literalMember).trans atomEq

/-- Both polarity operations that retain an original variable decode to
this occurrence's instantiated Figure 9 atom. -/
theorem OccurrenceWitness.originalPolarityAtom
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (original : occurrence.header.polarity.operation = .compatible ∨
      occurrence.header.polarity.operation = .complementOriginal)
    (atom : PolarityNormalizedVariable
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (decoded :
      (PeriodicOneInThreePolarityNormalizationRouteSubdivision.sourceIndexedDescriptorOf
        occurrence.generatedClauseIndex occurrence.header.polarity.indexed).atom?
        (PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinedSource
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
            source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source)).erase =
        some atom) :
    let query := occurrence.header.figurePrefix.localQuery
    atom = .inl (instantiatedVariableMap witness.metadata.sourceClauseIndex
      witness.metadata.figureNineClauseStart witness.metadata.sourceClause
      ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1) := by
  obtain ⟨clause, clauseLookup, decodedLiteral⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨literal, literalLookup, atomEq⟩ := Option.map_eq_some_iff.mp decodedLiteral
  have selected := witness.refinedFinalGaugedLiteralAtom
    sourceLocal sourceWidth sourceOccurrences sourceNonempty clauseLookup literalLookup
  dsimp only
  rw [selected]
  rcases original with original | original <;>
    simpa only [PeriodicOneInThreePolarityNormalizationRouteSubdivision.sourceIndexedDescriptorOf,
      ClauseProfilePolarityRouteOperation.Descriptor.indexed, original] using atomEq.symm

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
