/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceLocalRoutes
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixOrderedFanSemantics

/-! # Exact inherited connectors selected by Figure 9 occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNineRoutePrefix

open FormulaShapeDirectionOrdering
open ClauseProfilePolarityRouteOperation
open PlanarOneInThreeNoUnitsFigureNine

/-- An inherited descriptor retains its exact profile, local incidence,
reconstructed fan, and source slot. -/
theorem descriptorAt_inherited_query
    (profile : DirectedClauseProfile)
    (index : Fin (templateDrawingOfClauseProfile (clauseProfile profile)).incidences.length)
    (slot : SourceLiteralSlot) (query : LocalExtendedDirectionQuery)
    (descriptorEq : descriptorAt profile index = .inherited slot query) :
    query = ⟨clauseProfile profile, index, exitFanData profile, sourceSlotFin slot⟩ := by
  unfold descriptorAt at descriptorEq
  dsimp only at descriptorEq
  split at descriptorEq
  · contradiction
  · cases descriptorEq
    rfl

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNineRoutePrefix

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeDirectionOrdering
open ClauseProfilePolarityRouteOperation
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

/-- The connector stored in an inherited header is exactly the connector
of its metadata's clearance-scaled geometric source clause. -/
theorem OccurrenceWitness.inheritedConnector
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (slot : SourceLiteralSlot) (query : LocalExtendedDirectionQuery)
    (prefixEq : occurrence.header.figurePrefix = .inherited slot query) :
    query.2.2.1.extendedRoute query.2.2.2 =
      (PositionedPeriodicCNF.clauseExitFanData witness.metadata.sourceClause
        witness.metadata.sourceClauseIndex
        (retainedFigureNineClearanceIncidenceRoutes source)).extendedRoute (sourceSlotFin slot) := by
  obtain ⟨index, descriptorEq⟩ :=
    exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
      occurrence.profile occurrence.header witness.headerMember
  have inheritedEq := descriptorEq.trans prefixEq
  have slotLt := descriptorAt_inherited_sourceSlotNat_lt
    (orderedDirectedProfile occurrence.profile) index slot query inheritedEq
  have queryEq := descriptorAt_inherited_query
    (orderedDirectedProfile occurrence.profile) index slot query inheritedEq
  have slotVal : (sourceSlotFin slot).val = sourceSlotNat slot := by cases slot <;> rfl
  have profileLength :
      (clauseProfile (orderedDirectedProfile occurrence.profile)).literals.length =
        witness.refinedClause.literals.length := by
    rw [witness.profileEq, clauseProfile_orderedDirectedProfile,
      DirectedClauseProfile.orderedProfile_ofClause_literals _ _ _
        witness.refinedNonempty witness.refinedWidth]
    simp only [ClauseProfileOccurrenceSplit.literalProfiles, List.length_map,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length]
  have active : (sourceSlotFin slot).val < witness.refinedClause.literals.length := by
    rwa [slotVal, ← profileLength]
  have orderedDirection := exitFanData_direction_ordered_ofClause
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
    occurrence.parentClauseIndex witness.refinedClause witness.sourceLookup
    witness.refinedNonempty witness.refinedWidth (sourceSlotFin slot) active
  have parentEq : witness.metadata.sourceClauseIndex = occurrence.parentClauseIndex :=
    congrArg Prod.fst witness.metadataKey
  have sourceActive : (sourceSlotFin slot).val < witness.metadata.sourceClause.literals.length := by
    simpa only [witness.metadataSource, PositionedPeriodicClause.scale_literals,
      PositionedPeriodicCNF.orderClauseByRouteDirection_length] using active
  have metadataValid := formulaClauseMetadata_valid
    (retainedFigureNineClearancePositionedFormula source)
    (List.mem_iff_getElem?.mpr ⟨occurrence.generatedClauseIndex, witness.metadataLookup⟩)
  have sourceLiteralMember :
      (witness.metadata.sourceClause.literals[(sourceSlotFin slot).val],
        (sourceSlotFin slot).val) ∈ witness.metadata.sourceClause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem sourceActive)
  have clearanceDirection := retainedFigureNineClearanceIncidenceRoutes_firstDirection
    source sourceLocal sourceWidth sourceOccurrences sourceNonempty
    metadataValid.1 sourceLiteralMember
  rw [parentEq] at clearanceDirection
  have directionEq :
      (exitFanData (orderedDirectedProfile occurrence.profile)).direction (sourceSlotFin slot) =
        (PositionedPeriodicCNF.clauseExitFanData witness.metadata.sourceClause
          witness.metadata.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source)).direction (sourceSlotFin slot) := by
    rw [witness.profileEq, orderedDirection]
    simpa only [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes,
      PositionedPeriodicCNF.clauseExitFanData, parentEq] using clearanceDirection.symm
  rw [queryEq]
  dsimp only
  unfold ComposedClauseExitFanData.extendedRoute ComposedClauseExitFanData.route
  rw [directionEq]

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
