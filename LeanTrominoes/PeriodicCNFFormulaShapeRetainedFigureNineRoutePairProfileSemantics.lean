/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixLocalDirectionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderPrefixSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRoutePairSourceProvenance
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PositionedPeriodicCNFEraseMembership

/-! # Source profiles selected by retained Figure 9 route pairs -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeFigureNineSourceTail
open PlanarOneInThreeNoUnitsFigureNine
open PeriodicOrthocrossing

/-- Every retained pair selects the canonical profile of the exact scaled
clockwise source clause that is subsequently expanded by Figure 9. -/
theorem exists_clearanceSourceClause_of_mem_sourcePairs
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (pair : FormulaShapeFigureNinePolarityRouteHeader.Header ×
      List AxisDirection)
    (pairMember : pair ∈
      FormulaShapeFigureNinePolarityRouteTail.sourcePairs
        (FormulaShapeRetainedFigureNineDirection.descriptors source)
        (tailTables source)) :
    ∃ refinedClause clearanceClause clauseIndex,
      (refinedClause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx ∧
      clearanceClause =
        (PositionedPeriodicCNF.orderClauseByRouteDirection
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            source)
          clauseIndex refinedClause).scale
            retainedFigureNineSourceClearanceFactor ∧
      (clearanceClause, clauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx ∧
      pair.1 ∈ sourceClauseHeaders
        (DirectedClauseProfile.ofClause
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            source)
          clauseIndex refinedClause) ∧
      pair.2 =
        selectedTailDirections
          (orderedTailDirections
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              source)
            clauseIndex refinedClause)
          pair.1 ∧
      pair.1.figurePrefix.localQuery.1 =
        FormulaShapeOfFormula.clauseProfile
          (ClauseProfileOccurrenceSplit.literalProfiles
            clearanceClause.literals) := by
  rcases exists_sourceClause_of_mem_sourcePairs source pair pairMember with
    ⟨refinedClause, clauseIndex, refinedMember, headerMember, tailEq⟩
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
  let profile :=
    DirectedClauseProfile.ofClause routes clauseIndex refinedClause
  let clockwiseClause :=
    PositionedPeriodicCNF.orderClauseByRouteDirection
      routes clauseIndex refinedClause
  let clearanceClause :=
    clockwiseClause.scale retainedFigureNineSourceClearanceFactor
  have refinedNonempty : refinedClause.literals ≠ [] :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
      source sourceClausesNonempty refinedClause
      (List.fst_mem_of_mem_zipIdx refinedMember)
  have refinedWidth : refinedClause.literals.length ≤ 3 := by
    have widthAll :
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.WidthAtMost 3 :=
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth
    apply widthAll refinedClause.literals
    exact PositionedPeriodicCNF.literals_mem_erase_of_mem_zipIdx
      refinedMember
  have clockwiseMember :
      (clockwiseClause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx := by
    exact PositionedPeriodicCNF.orderClauseByRouteDirection_mem
      routes refinedMember
  have clearanceMember :
      (clearanceClause, clauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx := by
    rw [retainedFigureNineClearancePositionedFormula,
      PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr ⟨(clockwiseClause, clauseIndex),
      clockwiseMember, rfl⟩
  rcases
      exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
        profile pair.1 (by simpa only [profile, routes] using headerMember) with
    ⟨templateIndex, descriptorEq⟩
  have headerProfile :
      pair.1.figurePrefix.localQuery.1 =
        clauseProfile (orderedDirectedProfile profile) := by
    rw [← descriptorEq, localQuery_descriptorAt]
  have orderedProfile :=
    clauseProfile_orderedDirectedProfile_ofClause
      routes clauseIndex refinedClause refinedNonempty refinedWidth
  refine ⟨refinedClause, clearanceClause, clauseIndex,
    refinedMember, rfl, clearanceMember, headerMember, tailEq, ?_⟩
  calc
    pair.1.figurePrefix.localQuery.1 =
        clauseProfile (orderedDirectedProfile profile) := headerProfile
    _ = FormulaShapeOfFormula.clauseProfile
          (ClauseProfileOccurrenceSplit.literalProfiles
            clockwiseClause.literals) := by
      simpa only [profile, clockwiseClause] using orderedProfile
    _ = FormulaShapeOfFormula.clauseProfile
          (ClauseProfileOccurrenceSplit.literalProfiles
            clearanceClause.literals) := by
      rw [show clearanceClause.literals = clockwiseClause.literals by
        exact PositionedPeriodicClause.scale_literals _ _]

end FormulaShapeRetainedFigureNineSourceTail
end PeriodicCNF
end LeanTrominoes
