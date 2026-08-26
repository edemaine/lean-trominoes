/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCrossoverNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairNextSliceNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairOwnershipNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairData

/-! # Numeric semantics of sparse retained carrier-pair masks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open SignedUnaryStrictLower

/-- Semantic retained-pair predicate on globally enumerated indexed data. -/
def retainedPredicate
    (first second : (CarrierNodeRankDatum × Nat) × Nat) : Bool :=
  ((decide (first.1.1.key = second.1.1.key) &&
      decide (second.2 = first.2 + 1)) &&
    !first.1.1.sameCrossoverSite second.1.1) &&
    first.1.1.pairIsRepresentative second.1.1

private theorem matrix_zipIdx_fst
    {Value : Type*} (values : List Value)
    (predicate : Value → Value → Bool) :
    matrix values predicate =
      matrix values.zipIdx fun first second =>
        predicate first.1 second.1 := by
  unfold matrix matrixRows
  conv_lhs =>
    rw [← List.zipIdx_map_fst 0 values]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  rw [List.map_map]
  rfl

/-- The compiled retained mask selects exactly globally consecutive,
same-key, non-crossover, zero-owner pairs. -/
theorem retainedMaskBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedMaskBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries.zipIdx retainedPredicate := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have candidateEq := bits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have differentEq := differentCrossoverBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  rw [matrix_zipIdx_fst entries
    (fun first second => !first.1.sameCrossoverSite second.1)] at differentEq
  have representativeEq := representativeBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  rw [matrix_zipIdx_fst entries
    (fun first second => first.1.pairIsRepresentative second.1)]
    at representativeEq
  unfold retainedMaskBits nonCrossoverCandidateBits combined
  change pairwise .conjunction
      (pairwise .conjunction
        (bits (PeriodicCNF.numericRouteDescriptors formula))
        (differentCrossoverBits
          (PeriodicCNF.numericRouteDescriptors formula)))
      (representativeBits
        (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [candidateEq, differentEq, representativeEq,
    pairwise_matrix, pairwise_matrix]
  rfl

/-- The masked axis stream retains exactly the first endpoint's axis on
selected pairs. -/
theorem retainedAxisBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedAxisBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries.zipIdx fun first second =>
        retainedPredicate first second && first.1.1.horizontal := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have maskEq := retainedMaskBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have axisEq := axisBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  rw [matrix_zipIdx_fst entries
    (fun first _second => first.1.horizontal)] at axisEq
  unfold retainedAxisBits combined
  change pairwise .conjunction
      (retainedMaskBits (PeriodicCNF.numericRouteDescriptors formula))
      (axisBits (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [maskEq, axisEq, pairwise_matrix]
  rfl

/-- The masked next-slice stream retains exactly the selected pairs'
next-slice bit. -/
theorem retainedNextSliceBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedNextSliceBits
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries.zipIdx fun first second =>
        retainedPredicate first second &&
          first.1.1.pairNextSlice second.1.1 := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have maskEq := retainedMaskBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  have nextEq := nextSliceBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
  rw [matrix_zipIdx_fst entries
    (fun first second => first.1.pairNextSlice second.1)] at nextEq
  unfold retainedNextSliceBits combined
  change pairwise .conjunction
      (retainedMaskBits (PeriodicCNF.numericRouteDescriptors formula))
      (nextSliceBits (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [maskEq, nextEq, pairwise_matrix]
  rfl

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
