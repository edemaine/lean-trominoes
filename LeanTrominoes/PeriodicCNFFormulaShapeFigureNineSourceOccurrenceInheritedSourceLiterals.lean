/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPresentationSlotSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAtomClassification

/-! # Exact presentation literals selected by inherited Figure 9 occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNinePolarityRouteHeader
open ClauseProfilePolarityRouteOperation
open PlanarOneInThreeNoUnitsFigureNine
open PeriodicOrthocrossing
open PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope

private theorem localQuery_sourceSlotNat_lt
    (query : LocalDirectionQuery) (slot : SourceLiteralSlot)
    (selected : sourceSlot?
      ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 = some slot) :
    sourceSlotNat slot < query.1.literals.length := by
  rcases query with ⟨profile, index⟩
  cases profile <;> native_decide +revert

/-- The local query's complete source-literal profile is the actual profile
of the occurrence's own clockwise parent. -/
theorem OccurrenceWitness.localQueryProfile_literals
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) :
    occurrence.header.figurePrefix.localQuery.1.literals =
      ClauseProfileOccurrenceSplit.literalProfiles witness.metadata.sourceClause.literals := by
  have sourceWidth : witness.metadata.sourceClause.literals.length ≤ 3 := by
    simpa only [witness.metadataSource, PositionedPeriodicClause.scale_literals,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length] using witness.refinedWidth
  have profileEq := witness.metadataCoordinates.1
  change occurrence.header.figurePrefix.localQuery.1 =
    witness.metadata.parentProfileCoordinate.profile at profileEq
  rw [profileEq]
  exact FormulaShapeOfFormula.clauseProfile_literals _
    (by simpa [ClauseProfileOccurrenceSplit.literalProfiles] using witness.sourceClause_nonempty)
    (by simpa [ClauseProfileOccurrenceSplit.literalProfiles] using sourceWidth)

/-- Every inherited role of a genuine occurrence selects an active source
literal in its actual clockwise parent. -/
theorem OccurrenceWitness.inheritedSourceSlot_lt
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot?
      ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
        occurrence.header.figurePrefix.localQuery.2).literal.1 = some slot) :
    sourceSlotNat slot < witness.metadata.sourceClause.literals.length := by
  have bound := localQuery_sourceSlotNat_lt occurrence.header.figurePrefix.localQuery slot selected
  simpa only [witness.localQueryProfile_literals,
    ClauseProfileOccurrenceSplit.literalProfiles, List.length_map] using bound

/-- The inherited atom and the compiled inverse-permutation slot select the
same literal in the original, unsorted parent presentation. -/
theorem OccurrenceWitness.inheritedSourceLiteral
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot?
      ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
        occurrence.header.figurePrefix.localQuery.2).literal.1 = some slot) :
    ∃ literal,
      witness.refinedClause.literals[sourceSlotNat (presentationSlotAt occurrence.profile slot)]? = some literal ∧
      instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
        witness.metadata.sourceClause
        ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
          occurrence.header.figurePrefix.localQuery.2).literal.1 = .inl (.inl literal.atom) := by
  have active := witness.inheritedSourceSlot_lt slot selected
  have refinedActive : sourceSlotNat slot < witness.refinedClause.literals.length := by
    simpa only [witness.metadataSource, PositionedPeriodicClause.scale_literals,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length] using active
  let literal := witness.metadata.sourceClause.literals[sourceSlotNat slot]
  have literalLookup : witness.metadata.sourceClause.literals[sourceSlotNat slot]? = some literal :=
    List.getElem?_eq_getElem active
  have transport := orderClause_literal_lookup_at_presentationSlot
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
    occurrence.parentClauseIndex witness.refinedClause witness.refinedNonempty witness.refinedWidth
    slot refinedActive
  have sourceLookup :
      witness.metadata.sourceClause.literals[sourceSlotNat slot]? =
        witness.refinedClause.literals[sourceSlotNat (presentationSlotAt occurrence.profile slot)]? := by
    simpa only [witness.metadataSource, PositionedPeriodicClause.scale_literals, ← witness.profileEq] using transport
  exact ⟨literal, sourceLookup.symm.trans literalLookup,
    instantiatedVariableMap_of_sourceSlot_some witness.metadata.sourceClauseIndex
      witness.metadata.figureNineClauseStart witness.metadata.sourceClause _ slot selected active⟩

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
