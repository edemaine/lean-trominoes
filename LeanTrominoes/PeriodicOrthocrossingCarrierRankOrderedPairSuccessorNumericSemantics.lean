/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairData

/-! # Numeric semantics of rank-ordered position successors -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open CarrierRankDatumCompiledFields
open SignedUnaryStrictLower

private theorem sub_eq_one_iff (first second : Nat) :
    second - first = 1 ↔ second = first + 1 := by
  omega

/-- The excess/exact-one pipeline tests immediate succession in the
reconstructed rank-position column. -/
theorem successorBits_eq_flatMap (descriptors : List RouteDescriptor) :
    successorBits descriptors =
      (positions descriptors).flatMap fun first =>
        (positions descriptors).map fun second =>
          decide (second = first + 1) := by
  unfold successorBits positionExcesses positionWordPairs
  rw [UnaryExactOneBooleans.bits_eq_map]
  unfold DelimitedBinaryWordPairExcessMachine.excesses
    DelimitedBinaryWordPairProductMachine.pairs
    UnaryFieldBinaryWords.words
  simp only [List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]
  apply List.flatMap_congr
  intro first _firstMember
  apply List.map_congr_left
  intro second _secondMember
  simp [DelimitedBinaryWordPairExcessMachine.excess,
    UnaryFieldBinaryWords.word, sub_eq_one_iff]

/-- On numeric routes, position succession is exactly immediate `zipIdx`
succession in the global carrier enumeration. -/
theorem successorBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    successorBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries.zipIdx fun first second =>
        decide (second.2 = first.2 + 1) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have valuesEq := Field.rankOrderedValues_numericRouteDescriptors
    .keyRoute formula wellFormed degree isLocal forward nonempty
  change Field.rankOrderedValues .keyRoute descriptors =
    entries.map fun entry => entry.1.scanUnaryFields.getD 0 0 at valuesEq
  have positionsEq : positions descriptors = List.range entries.length := by
    unfold positions UnaryFieldRange.values
    rw [valuesEq]
    simp
  rw [successorBits_eq_flatMap, positionsEq]
  have rangeEq :
      List.range entries.length = entries.zipIdx.map Prod.snd := by
    rw [List.zipIdx_map_snd, List.range_eq_range']
  rw [rangeEq]
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  rfl

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
