/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountSemantics
import LeanTrominoes.ListSplitLengthsFlatMapFixed
import LeanTrominoes.ListZipIdxMapSemantics
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankCountSemantics
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankPipelineData
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of the global occurrence stable-rank pipeline -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

variable {Variable : Type*} [DecidableEq Variable]

/-- Square reshaping recovers the strict-lower comparison rows exactly. -/
theorem retainedOccurrenceGlobalStableLowerDelimitedRows_words
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableLowerDelimitedRows
      source routes).words =
      retainedOccurrenceGlobalStableLowerRows source routes := by
  unfold retainedOccurrenceGlobalStableLowerDelimitedRows
    BoolSquareRows.Input.delimitedRows BoolSquareRows.Input.rows
    BoolSquareRows.Input.sizes
  rw [retainedOccurrenceGlobalStableLowerSquareInput_side]
  unfold retainedOccurrenceGlobalStableLowerSquareInput
    retainedOccurrenceGlobalStableLowerBits
    retainedOccurrenceGlobalStableLowerRows
  dsimp only
  exact List.replicate_splitLengths_flatMap_of_length_eq
    (allOccurrenceVariables source)
    (fun target =>
      (allOccurrenceVariables source).map
        (retainedOccurrenceGlobalStableLowerPredicate routes target))
    (allOccurrenceVariables source).length (by intro; simp)

/-- Square reshaping recovers the equal-coordinate comparison rows exactly. -/
theorem retainedOccurrenceGlobalStableTieDelimitedRows_words
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTieDelimitedRows
      source routes).words =
      retainedOccurrenceGlobalStableTieRows source routes := by
  unfold retainedOccurrenceGlobalStableTieDelimitedRows
    BoolSquareRows.Input.delimitedRows BoolSquareRows.Input.rows
    BoolSquareRows.Input.sizes
  rw [retainedOccurrenceGlobalStableTieSquareInput_side]
  unfold retainedOccurrenceGlobalStableTieSquareInput
    retainedOccurrenceGlobalStableTieBits
    retainedOccurrenceGlobalStableTieRows
  dsimp only
  exact List.replicate_splitLengths_flatMap_of_length_eq
    (allOccurrenceVariables source)
    (fun target =>
      (allOccurrenceVariables source).map
        (retainedOccurrenceGlobalStableTiePredicate routes target))
    (allOccurrenceVariables source).length (by intro; simp)

/-- The strict-lower counter output is the presentation-ordered list of full
row true counts. -/
theorem retainedOccurrenceGlobalStableLowerCounts_eq
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableLowerCounts source routes =
      (allOccurrenceVariables source).map fun target =>
        ((allOccurrenceVariables source).map
          (retainedOccurrenceGlobalStableLowerPredicate routes target)).count
          true := by
  unfold retainedOccurrenceGlobalStableLowerCounts
    DelimitedBinaryWordTrueCounts.counts
    DelimitedBinaryWordTrueCounts.countTrue
  rw [retainedOccurrenceGlobalStableLowerDelimitedRows_words]
  unfold retainedOccurrenceGlobalStableLowerRows
  rw [List.map_map]
  rfl

/-- The equal-coordinate counter output takes the successively longer prefix
ending immediately before each row's diagonal entry. -/
theorem retainedOccurrenceGlobalStableTieCounts_eq
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableTieCounts source routes =
      (allOccurrenceVariables source).zipIdx.map fun entry =>
        (((allOccurrenceVariables source).map
          (retainedOccurrenceGlobalStableTiePredicate
            routes entry.1)).take entry.2).count true := by
  unfold retainedOccurrenceGlobalStableTieCounts
    DelimitedBinaryWordPrefixTrueCounts.counts
  rw [retainedOccurrenceGlobalStableTieDelimitedRows_words]
  simpa [retainedOccurrenceGlobalStableTieRows,
    DelimitedBinaryWordPrefixTrueCounts.count] using
    (DelimitedBinaryWordPrefixTrueCounts.countsAux_map
      (allOccurrenceVariables source)
      (fun target =>
        (allOccurrenceVariables source).map
          (retainedOccurrenceGlobalStableTiePredicate routes target)) 0)

/-- The square reshapers, row counters, prefix counters, and aligned unary
addition compute exactly the count-defined global stable-rank stream. -/
theorem retainedOccurrenceGlobalStableRankPipeline_eq_counts
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableRankPipeline source routes =
      retainedOccurrenceGlobalStableTerminalRankCounts source routes := by
  unfold retainedOccurrenceGlobalStableRankPipeline
  have valid : UnaryAlignedAddMachine.Valid
      (retainedOccurrenceGlobalStableLowerCounts source routes)
      (retainedOccurrenceGlobalStableTieCounts source routes) :=
    (retainedOccurrenceGlobalStableRankAdditionInput source routes).valid
  rw [UnaryAlignedAddMachine.sums_eq_zipWith valid]
  rw [retainedOccurrenceGlobalStableLowerCounts_eq,
    retainedOccurrenceGlobalStableTieCounts_eq]
  rw [LeanTrominoes.List.zipWith_map_zipIdx]
  rfl

/-- Therefore the complete square-count pipeline computes the semantic
global stable terminal ranks. -/
theorem retainedOccurrenceGlobalStableRankPipeline_eq
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableRankPipeline source routes =
      retainedOccurrenceGlobalStableTerminalRanks source routes := by
  rw [retainedOccurrenceGlobalStableRankPipeline_eq_counts,
    retainedOccurrenceGlobalStableTerminalRankCounts_eq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
