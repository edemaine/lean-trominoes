/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataClauseArity
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalDirectionBlock
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalDirectionQueryCoordinates

/-! # Exact local routes selected by Figure 9 source occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNineFinalClauseOrdering
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine
open Gadget

variable {Variable : Type} [DecidableEq Variable]
variable {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}

/-- The occurrence's generated clause belongs to the raw geometric formula
at exactly its recorded absolute index. -/
theorem OccurrenceWitness.rawClauseMember
    (witness : OccurrenceWitness source occurrence) :
    (witness.metadata.clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).clauses.zipIdx := by
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  change (PeriodicOneInThreeNoUnitsPositioned.formula
    (PeriodicOneInThreePositioned.formula
      (retainedFigureNineClearancePositionedFormula source))).clauses[
        occurrence.generatedClauseIndex]? = some witness.metadata.clause
  rw [← formulaClauseMetadata_clauses, List.getElem?_map, witness.metadataLookup]
  rfl

/-- Both the header's final literal index and its original raw index are in
bounds; the two indices are related by the exact clockwise permutation. -/
theorem OccurrenceWitness.rawLiteralCoordinates
    (witness : OccurrenceWitness source occurrence)
    (width : source.WidthAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    let coordinate := headerTemplateCoordinate occurrence.header
    coordinate.polarity.sourceLiteralIndex < witness.metadata.clause.literals.length ∧
    coordinate.literalIndex =
      (reorderList (List.range witness.metadata.clause.literals.length)).getD
        coordinate.polarity.sourceLiteralIndex 0 ∧
    coordinate.literalIndex < witness.metadata.clause.literals.length := by
  obtain ⟨_, _, indexEq, indexLt⟩ := witness.metadataCoordinates
  have arityEq := metadata_clause_length_eq_parentProfileCoordinate_literalCount
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePositionedFormula_clausesNonempty source nonempty)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree source width)
    (List.mem_iff_getElem?.mpr ⟨occurrence.generatedClauseIndex, witness.metadataLookup⟩)
  rw [← arityEq] at indexEq indexLt
  dsimp only [headerTemplateProfileCoordinate] at indexEq indexLt
  refine ⟨indexLt, indexEq, ?_⟩
  rw [indexEq]
  have reorderedLt :
      (headerTemplateCoordinate occurrence.header).polarity.sourceLiteralIndex <
        (reorderList (List.range witness.metadata.clause.literals.length)).length := by
    simpa only [reorderList_length, List.length_range] using indexLt
  rw [List.getD_eq_getElem _ _ reorderedLt]
  exact List.mem_range.mp (mem_of_mem_reorderList (List.getElem_mem reorderedLt))

/-- A header's finite local query agrees with any geometric query carrying
the same metadata and raw literal coordinate. -/
theorem OccurrenceWitness.localQuery_eq
    (witness : OccurrenceWitness source occurrence)
    (query : LocalDirectionQuery)
    (profileEq : query.1 = witness.metadata.parentProfileCoordinate.profile)
    (clauseEq : ((templateDrawingOfClauseProfile query.1).incidenceAt
      query.2).clauseIndex = witness.metadata.localClauseIndex)
    (literalEq : ((templateDrawingOfClauseProfile query.1).incidenceAt
      query.2).literalIndex = (headerTemplateCoordinate occurrence.header).literalIndex) :
    occurrence.header.figurePrefix.localQuery = query := by
  obtain ⟨headerProfile, headerClause, _, _⟩ := witness.metadataCoordinates
  apply LocalDirectionQuery.eq_of_profile_and_coordinates
  · exact headerProfile.trans profileEq.symm
  · exact headerClause.trans clauseEq.symm
  · exact literalEq.symm

/-- The executable header selects the complete normalized direction word of
the local geometric route at its own raw clause/literal incidence. -/
theorem OccurrenceWitness.localDirectionWord
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    normalizedLocalDirectionBlock occurrence.header.figurePrefix.localQuery =
      unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (normalizedLocalRoutes
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)
            occurrence.generatedClauseIndex
            (headerTemplateCoordinate occurrence.header).literalIndex)) := by
  have literalLt := (witness.rawLiteralCoordinates sourceWidth sourceNonempty).2.2
  have literalMember :
      (witness.metadata.clause.literals[
        (headerTemplateCoordinate occurrence.header).literalIndex],
        (headerTemplateCoordinate occurrence.header).literalIndex) ∈
          witness.metadata.clause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem literalLt)
  obtain ⟨metadata, query, metadataLookup, _, profileEq, directionsEq,
      clauseEq, literalEq⟩ := normalizedLocalRoutes_directionBlock_of_members
    (retainedFigureNineClearancePositionedFormula source)
    (retainedFigureNineClearancePlacement source)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree source sourceWidth)
    (retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
    (retainedFigureNineClearancePositionedFormula_clausesNonempty source sourceNonempty)
    witness.rawClauseMember literalMember
  have metadataEq : metadata = witness.metadata :=
    Option.some.inj (metadataLookup.symm.trans witness.metadataLookup)
  subst metadata
  rw [witness.localQuery_eq query profileEq clauseEq literalEq]
  exact directionsEq.symm

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
