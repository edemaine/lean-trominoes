/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLocalRoutes

/-! # Actual literal atoms selected by Figure 9 occurrence headers -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

/-- The local incidence selected by the executable header instantiates to
the actual literal at the occurrence's raw geometric coordinate. -/
theorem OccurrenceWitness.literalAtom
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceWidth : source.WidthAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (literalMember :
      (literal, (headerTemplateCoordinate occurrence.header).literalIndex) ∈
        witness.metadata.clause.literals.zipIdx) :
    let query := occurrence.header.figurePrefix.localQuery
    instantiatedVariableMap witness.metadata.sourceClauseIndex
        witness.metadata.figureNineClauseStart witness.metadata.sourceClause
        ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 =
      literal.atom := by
  obtain ⟨metadata, profile, index, _, metadataLookup, _, profileEq, _,
      clauseEq, literalEq, atomEq⟩ :=
    normalizedLocalRoutes_eq_translated_profileRoute_of_members
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_clausesNonempty source sourceNonempty)
      witness.rawClauseMember literalMember
  have metadataEq : metadata = witness.metadata :=
    Option.some.inj (metadataLookup.symm.trans witness.metadataLookup)
  subst metadata
  have queryEq := witness.localQuery_eq ⟨profile, index⟩ profileEq clauseEq literalEq
  dsimp only
  rw [queryEq]
  exact atomEq

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
