/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLiteralAtoms
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixInstantiationSemantics
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineAuxiliaryRouteDirectionBlock

/-! # Complete auxiliary route words selected by Figure 9 occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine
open Gadget

local instance occurrenceAuxiliaryVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  nestedVariableDecidableEq

/-- A local header denotes the complete raw auxiliary route word, since
its actual literal is auxiliary and hence receives no inherited suffix. -/
theorem OccurrenceWitness.auxiliaryDirectionWord
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (query : LocalDirectionQuery)
    (prefixEq : occurrence.header.figurePrefix = .local query) :
    unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty
          occurrence.generatedClauseIndex
          (headerTemplateCoordinate occurrence.header).literalIndex)) =
      normalizedLocalDirectionBlock query := by
  have literalLt := (witness.rawLiteralCoordinates sourceWidth sourceNonempty).2.2
  let literal := witness.metadata.clause.literals[
    (headerTemplateCoordinate occurrence.header).literalIndex]
  have literalMember :
      (literal, (headerTemplateCoordinate occurrence.header).literalIndex) ∈
        witness.metadata.clause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem literalLt)
  have atomEq := witness.literalAtom sourceWidth sourceNonempty literalMember
  have classified := sourceSlot_header occurrence.profile occurrence.header witness.headerMember
  rw [prefixEq] at atomEq classified
  have notInherited : ∀ atom, literal.atom ≠ .inl (.inl atom) := by
    intro atom
    rw [← atomEq]
    exact instantiatedVariableMap_not_inherited_of_sourceSlot_none
      witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
      witness.metadata.sourceClause
      ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1 classified atom
  obtain ⟨metadata, actualQuery, metadataLookup, _, profileEq, directionsEq,
      clauseEq, literalEq⟩ := retainedOrderedFixedEightFigureNineAuxiliaryRoute_directionBlock
    source sourceLocal sourceWidth sourceOccurrences sourceNonempty
    witness.rawClauseMember literalMember notInherited
  have metadataEq : metadata = witness.metadata :=
    Option.some.inj (metadataLookup.symm.trans witness.metadataLookup)
  subst metadata
  have queryEq := witness.localQuery_eq actualQuery profileEq clauseEq literalEq
  rw [prefixEq] at queryEq
  exact directionsEq.trans (congrArg normalizedLocalDirectionBlock queryEq.symm)

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
