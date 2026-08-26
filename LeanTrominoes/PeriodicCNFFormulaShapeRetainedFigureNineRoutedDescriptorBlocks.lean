/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionData

/-! # Routed descriptor blocks of the retained Figure 9 formula -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing

/-- The final positioned fixed-eight formula is exactly its copied-clause
prefix followed by its positioned implication-cycle suffix. -/
theorem finalPositionedFormula_clauses_eq_descriptorBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source).clauses =
      copiedOccurrenceClauses source ++ finalCycleClauses source := by
  unfold
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    PeriodicEightOccurrenceSplit.retainedAngularFanSourceScaledRefinedFormula
    PeriodicEightOccurrenceSplit.retainedAngularFanRefinedFormula
  rw [PositionedPeriodicCNF.scale_clauses]
  unfold PeriodicEightOccurrenceSplitPositioned.formula
  rw [List.map_append]
  apply congrArg₂ List.append
  · unfold copiedOccurrenceClauses copiedOccurrenceClause
    unfold occurrencePortsForFigureSeven sourceScaledForFigureSeven
      routesScaledForFigureSeven finalCoordinatedSource
      finalCoordinatedSourceRoutes
    unfold PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map, List.map_map, List.map_map]
    apply List.map_congr_left
    rintro ⟨clause, clauseIndex⟩ _clauseMember
    rfl
  · rfl

/-- The explicit copied prefix has exactly the append-boundary length used
by the global cycle-route indices. -/
theorem copiedOccurrenceClauses_length_eq_copiedClauseCount
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedOccurrenceClauses source).length =
      copiedClauseCount source := by
  unfold copiedOccurrenceClauses copiedClauseCount
    PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
    sourceScaledForFigureSeven
  simp

/-- Re-indexing the pointwise copied-clause construction preserves the
source clause index used by its route lookup. -/
theorem copiedOccurrenceClauses_zipIdx_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedOccurrenceClauses source).zipIdx =
      (finalCoordinatedSource source).clauses.zipIdx.map fun taggedClause =>
        (copiedOccurrenceClause source taggedClause.2 taggedClause.1,
          taggedClause.2) := by
  unfold copiedOccurrenceClauses
  exact List.zipIdx_map_zipIdx
    (finalCoordinatedSource source).clauses
    (fun taggedClause =>
      copiedOccurrenceClause source taggedClause.2 taggedClause.1)

/-- Re-indexing the pointwise copied-clause construction preserves the
source clause index used by its route lookup. -/
theorem copiedOccurrenceClauseTokens_eq_routedCopiedClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (copiedOccurrenceClauses source).zipIdx.map (fun taggedClause =>
        FormulaShapeDirectionOrdering.Token.clause
          (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              source)
            taggedClause.2 taggedClause.1)) =
      routedCopiedClauseDescriptors source := by
  rw [copiedOccurrenceClauses_zipIdx_eq, List.map_map]
  unfold routedCopiedClauseDescriptors routedCopiedClauseProfile
  rfl

/-- Indexing the cycle suffix from the copied-prefix length is exactly the
global index arithmetic stored by `routedCycleClauseDescriptors`. -/
theorem shiftedCycleClauseTokens_eq_routedCycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((finalCycleClauses source).zipIdx
        (copiedOccurrenceClauses source).length).map (fun taggedClause =>
      FormulaShapeDirectionOrdering.Token.clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            source)
          taggedClause.2 taggedClause.1)) =
      routedCycleClauseDescriptors source := by
  rw [copiedOccurrenceClauses_length_eq_copiedClauseCount]
  unfold routedCycleClauseDescriptors
  rw [List.zipIdx_eq_map_add, List.map_map]
  rfl

/-- The descriptor stream computed directly from the final formula and route
family is exactly the named phase-major routed descriptor stream. -/
theorem descriptors_eq_routedDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    descriptors source = routedDescriptors source := by
  unfold descriptors routedDescriptors
    FormulaShapeDirectionOrdering.ofFormula
  rw [finalPositionedFormula_clauses_eq_descriptorBlocks,
    List.zipIdx_append, List.map_append]
  simp only [Nat.zero_add]
  rw [copiedOccurrenceClauseTokens_eq_routedCopiedClauseDescriptors,
    shiftedCycleClauseTokens_eq_routedCycleClauseDescriptors]

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
