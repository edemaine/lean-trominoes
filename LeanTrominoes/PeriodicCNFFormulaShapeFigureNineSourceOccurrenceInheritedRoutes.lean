/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLiteralAtoms
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixInstantiationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedConnectors
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedRouteDirectionBlock

/-! # Complete inherited route words selected by Figure 9 occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeDirectionOrdering
open ClauseProfilePolarityRouteOperation
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine
open Gadget

private theorem literalIndex_eq_of_atom_eq
    {Variable : Type} [DecidableEq Variable]
    {clause : PositionedPeriodicClause Variable}
    (distinct : clause.AtomsNodup)
    {first second : PeriodicLiteral Variable} {firstIndex secondIndex : Nat}
    (firstMember : (first, firstIndex) ∈ clause.literals.zipIdx)
    (secondMember : (second, secondIndex) ∈ clause.literals.zipIdx)
    (atomEq : first.atom = second.atom) : firstIndex = secondIndex := by
  have firstLookup := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp firstMember)
  have secondLookup := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp secondMember)
  apply (List.getElem_inj
    (h₀ := by simpa using firstLookup.1)
    (h₁ := by simpa using secondLookup.1) distinct).mp
  simpa only [List.getElem_map, firstLookup.2, secondLookup.2] using atomEq

private theorem extendedDirectionBlock_eq
    (first second : LocalExtendedDirectionQuery)
    (localEq : (⟨first.1, first.2.1⟩ : LocalDirectionQuery) = ⟨second.1, second.2.1⟩)
    (connectorEq : first.2.2.1.extendedRoute first.2.2.2 =
      second.2.2.1.extendedRoute second.2.2.2) :
    normalizedLocalExtendedDirectionBlock first = normalizedLocalExtendedDirectionBlock second := by
  let localRoute (query : LocalDirectionQuery) :=
    (templateDrawingOfClauseProfile query.1).routeAt
      ((templateDrawingOfClauseProfile query.1).incidenceAt query.2)
  change unitSubdivisionDirections (AxisDirection.normalizeOrthogonalPolyline
      (joinAtEndpoint (localRoute ⟨first.1, first.2.1⟩)
        (first.2.2.1.extendedRoute first.2.2.2))) =
    unitSubdivisionDirections (AxisDirection.normalizeOrthogonalPolyline
      (joinAtEndpoint (localRoute ⟨second.1, second.2.1⟩)
        (second.2.2.1.extendedRoute second.2.2.2)))
  rw [localEq, connectorEq]

local instance occurrenceInheritedVariableDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  nestedVariableDecidableEq

/-- An inherited header and its paired tail denote the entire raw geometric
route word, with the exact active source slot and factor-144 tail repetition. -/
theorem OccurrenceWitness.inheritedDirectionWord
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (slot : SourceLiteralSlot) (query : LocalExtendedDirectionQuery)
    (prefixEq : occurrence.header.figurePrefix = .inherited slot query) :
    unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences sourceNonempty
          occurrence.generatedClauseIndex
          (headerTemplateCoordinate occurrence.header).literalIndex)) =
      normalizedLocalExtendedDirectionBlock query ++ repeatDirections 144 occurrence.pair.2 := by
  have literalLt := (witness.rawLiteralCoordinates sourceWidth sourceNonempty).2.2
  let literal := witness.metadata.clause.literals[
    (headerTemplateCoordinate occurrence.header).literalIndex]
  have literalMember :
      (literal, (headerTemplateCoordinate occurrence.header).literalIndex) ∈
        witness.metadata.clause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem literalLt)
  obtain ⟨index, descriptorEq⟩ :=
    exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
      occurrence.profile occurrence.header witness.headerMember
  have slotLt := descriptorAt_inherited_sourceSlotNat_lt
    (orderedDirectedProfile occurrence.profile) index slot query (descriptorEq.trans prefixEq)
  have profileLength :
      (clauseProfile (orderedDirectedProfile occurrence.profile)).literals.length =
        witness.metadata.sourceClause.literals.length := by
    rw [witness.profileEq, clauseProfile_orderedDirectedProfile,
      DirectedClauseProfile.orderedProfile_ofClause_literals _ _ _
        witness.refinedNonempty witness.refinedWidth, witness.metadataSource]
    simp only [ClauseProfileOccurrenceSplit.literalProfiles, List.length_map,
      PositionedPeriodicClause.scale_literals]
  have active : sourceSlotNat slot < witness.metadata.sourceClause.literals.length := by
    rwa [profileLength] at slotLt
  let sourceLiteral := witness.metadata.sourceClause.literals[sourceSlotNat slot]
  have sourceLiteralMember : (sourceLiteral, sourceSlotNat slot) ∈
      witness.metadata.sourceClause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem active)
  have atomEq := witness.literalAtom sourceWidth sourceNonempty literalMember
  have classified := sourceSlot_header occurrence.profile occurrence.header witness.headerMember
  rw [prefixEq] at atomEq classified
  have literalSource : literal.atom = .inl (.inl sourceLiteral.atom) :=
    atomEq.symm.trans (instantiatedVariableMap_of_sourceSlot_some
      witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
      witness.metadata.sourceClause
      ((templateDrawingOfClauseProfile query.1).incidenceAt query.2.1).literal.1
      slot classified active)
  obtain ⟨data, first, second, rest, actualQuery, _, routeEq, directionsEq,
      profileEq, clauseEq, literalEq, fanEq, slotEq⟩ :=
    retainedOrderedFixedEightFigureNineInheritedRoute_directionBlock
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty
      witness.rawClauseMember literalMember sourceLiteral.atom literalSource
  have metadataEq : data.metadata = witness.metadata :=
    Option.some.inj (data.metadataLookup.symm.trans witness.metadataLookup)
  have sourceClauseEq : data.sourceClause = witness.metadata.sourceClause :=
    data.metadataSourceClause.symm.trans (congrArg ClauseMetadata.sourceClause metadataEq)
  have sourceIndexEq : data.sourceClauseIndex = witness.metadata.sourceClauseIndex :=
    data.metadataSourceClauseIndex.symm.trans (congrArg ClauseMetadata.sourceClauseIndex metadataEq)
  have generatedClauseEq : data.generatedClause = witness.metadata.clause :=
    data.metadataClause.symm.trans (congrArg ClauseMetadata.clause metadataEq)
  have generatedMember := data.generatedLiteralMember
  rw [generatedClauseEq] at generatedMember
  have generatedLiteralEq : data.generatedLiteral = literal :=
    Option.some.inj ((List.mk_mem_zipIdx_iff_getElem?.mp generatedMember).symm.trans
      (List.mk_mem_zipIdx_iff_getElem?.mp literalMember))
  have sourceAtomEq : data.sourceLiteral.atom = sourceLiteral.atom := by
    have equality := data.literalAtom
    rw [generatedLiteralEq, literalSource] at equality
    exact Sum.inl.inj (Sum.inl.inj equality.symm)
  have dataSourceMember := data.sourceLiteralMember
  rw [sourceClauseEq] at dataSourceMember
  have distinct : witness.metadata.sourceClause.AtomsNodup := by
    apply retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences sourceNonempty
    rw [← sourceClauseEq]
    exact List.fst_mem_of_mem_zipIdx data.sourceClauseMember
  have sourceSlotEq : data.sourceLiteralIndex = sourceSlotNat slot :=
    literalIndex_eq_of_atom_eq distinct dataSourceMember sourceLiteralMember sourceAtomEq
  have queryEq := witness.localQuery_eq ⟨actualQuery.1, actualQuery.2.1⟩
    (by simpa only [sourceClauseEq, ClauseMetadata.parentProfileCoordinate] using profileEq)
    (by simpa only [metadataEq] using clauseEq) literalEq
  rw [prefixEq] at queryEq
  have geometricSlotEq : data.sourceSlot
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree source sourceWidth) =
        sourceSlotFin slot := by
    apply Fin.ext
    simpa only [InheritedIncidenceData.sourceSlot_val,
      show (sourceSlotFin slot).val = sourceSlotNat slot by cases slot <;> rfl] using sourceSlotEq
  have connectorEq : query.2.2.1.extendedRoute query.2.2.2 =
      actualQuery.2.2.1.extendedRoute actualQuery.2.2.2 := by
    rw [fanEq, slotEq, geometricSlotEq, sourceClauseEq, sourceIndexEq]
    exact witness.inheritedConnector sourceLocal sourceWidth sourceOccurrences sourceNonempty
      slot query prefixEq
  have prefixWordEq := extendedDirectionBlock_eq query actualQuery queryEq connectorEq
  have tailEq := witness.inheritedTail slot query prefixEq
  rw [← sourceIndexEq, ← sourceSlotEq, routeEq] at tailEq
  simp only [List.tail_cons] at tailEq
  rw [← prefixWordEq, ← tailEq] at directionsEq
  exact directionsEq

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
