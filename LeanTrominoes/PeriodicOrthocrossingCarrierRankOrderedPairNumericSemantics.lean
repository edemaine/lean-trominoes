/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairKeyNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairSuccessorNumericSemantics

/-! # Numeric semantics of rank-ordered carrier candidate pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open SignedUnaryStrictLower

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

/-- On numeric routes, the compiled candidate matrix marks exactly the
immediately consecutive global-enumeration entries belonging to one carrier
key. -/
theorem bits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    bits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize descriptors) descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      matrix entries.zipIdx fun first second =>
        decide (first.1.1.key = second.1.1.key) &&
          decide (second.2 = first.2 + 1) := by
  unfold bits combined
  change pairwise .conjunction
      (sameKeyBits (PeriodicCNF.numericRouteDescriptors formula))
      (successorBits (PeriodicCNF.numericRouteDescriptors formula)) = _
  rw [sameKeyBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
  rw [matrix_zipIdx_fst]
  rw [successorBits_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
  rw [pairwise_matrix]
  rfl

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
