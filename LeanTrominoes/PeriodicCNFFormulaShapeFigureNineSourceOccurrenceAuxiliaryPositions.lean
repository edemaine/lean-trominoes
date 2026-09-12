/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineAuxiliaryPositionSemantics
import LeanTrominoes.PeriodicVariablePlacementCanonicalGaugeLiteralPosition
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedSourceLiterals
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceFinalGaugedAtoms
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexBounds

/-! # Exact auxiliary coordinates selected by coherent Figure 9 occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine PeriodicOrthocrossing

local instance occurrenceAuxiliaryPositionVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)) := nestedVariableDecidableEq

private theorem localQuery_role_mem : ∀ query : LocalDirectionQuery,
    ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 ∈
      (templateDrawingOfClauseProfile query.1).variableVertices := by
  native_decide

/-- The exact header role gives the auxiliary's natural representative,
including the final canonical variable gauge. -/
theorem OccurrenceWitness.finalGaugedAuxiliaryPosition
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal) (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (auxiliary : sourceSlot?
      ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
        occurrence.header.figurePrefix.localQuery.2).literal.1 = none) :
    let role := ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
      occurrence.header.figurePrefix.localQuery.2).literal.1
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement source).position
      (instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
        witness.metadata.sourceClause role) =
      Cell.add (Cell.scale 72 witness.metadata.sourceClause.position) (variablePosition role) := by
  dsimp only
  let query := occurrence.header.figurePrefix.localQuery
  let role := ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1
  have literalLt := (witness.rawLiteralCoordinates sourceWidth sourceNonempty).2.2
  let literal := witness.metadata.clause.literals[(headerTemplateCoordinate occurrence.header).literalIndex]
  have literalMember : (literal, (headerTemplateCoordinate occurrence.header).literalIndex) ∈
      witness.metadata.clause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem literalLt)
  have atomEq := witness.literalAtom sourceWidth sourceNonempty literalMember
  have notInherited : ∀ atom, literal.atom ≠ .inl (.inl atom) := by
    intro atom
    rw [← atomEq]
    exact instantiatedVariableMap_not_inherited_of_sourceSlot_none _ _ _ _ auxiliary atom
  have physical := auxiliaryLiteralPosition_eq_instantiatedPosition
    (retainedFigureNineClearancePositionedFormula source) (retainedFigureNineClearancePlacement source)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree source sourceWidth)
    (retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty)
    witness.metadataLookup witness.rawClauseMember literalMember notInherited
  have sourceMember := (formulaClauseMetadata_valid
    (retainedFigureNineClearancePositionedFormula source)
    (List.mem_iff_getElem?.mpr ⟨occurrence.generatedClauseIndex, witness.metadataLookup⟩)).1
  have width : witness.metadata.sourceClause.literals.length ≤ 3 := by
    simpa only [witness.metadataSource, PositionedPeriodicClause.scale_literals,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length] using witness.refinedWidth
  have drawingEq : templateDrawingOfClauseProfile query.1 = templateDrawing witness.metadata.sourceClause := by
    have profileEq := witness.metadataCoordinates.1
    change query.1 = witness.metadata.parentProfileCoordinate.profile at profileEq
    rw [profileEq]
    exact templateDrawingOfClauseProfile_clauseProfile_literalProfiles
      witness.metadata.sourceClause witness.sourceClause_nonempty width
  have roleMember : role ∈ (templateDrawing witness.metadata.sourceClause).variableVertices := by
    rw [← drawingEq]
    exact localQuery_role_mem query
  have positionEq := instantiatedDrawing_rolePosition witness.metadata.sourceClauseIndex
    witness.metadata.figureNineClauseStart witness.metadata.sourceClause width
    (retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty
      witness.metadata.sourceClause (List.fst_mem_of_mem_zipIdx sourceMember)) role roleMember
  rw [templateDrawing_variablePosition] at positionEq
  have inside := retainedOrderedFixedEightComposedRawLocalLiteralPosition_inSquare
    source sourceLocal sourceWidth sourceOccurrences sourceNonempty
    witness.rawClauseMember literalMember notInherited
  have gauged := PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position_eq_literalPosition
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement source) literal
    ⟨le_of_lt inside.1, inside.2.1, le_of_lt inside.2.2.1, inside.2.2.2⟩
  rw [atomEq]
  exact gauged.trans (physical.trans (by simpa [role, query, atomEq, composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale] using positionEq))

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
