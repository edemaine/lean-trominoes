/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalSuccessorSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityNumericSemantics
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Numeric-route semantics of global carrier-rank successor bits -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobalSuccessor

open SignedUnaryStrictLower

private theorem matrix_map
    {Value Output : Type*} (values : List Value) (mapping : Value → Output)
    (predicate : Output → Output → Bool) :
    matrix (values.map mapping) predicate =
      matrix values fun first second =>
        predicate (mapping first) (mapping second) := by
  unfold matrix matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro value _valueMember
  simp [List.map_map, Function.comp_def]

/-- On valid numeric routes, the compiled conjunction marks exactly the
ordered indexed datum pairs with equal semantic keys and consecutive global
ranks. -/
theorem bits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    bits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      matrix datums.zipIdx fun first second =>
        decide (first.1.key = second.1.key) &&
          decide (CarrierRankGlobal.rankAt datums second =
            CarrierRankGlobal.rankAt datums first + 1) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  have keyBitsEq :
      CarrierRankKeyEquality.bits descriptors =
        matrix datums.zipIdx fun first second =>
          decide (first.1.key = second.1.key) := by
    calc
      CarrierRankKeyEquality.bits descriptors =
          matrix datums fun first second =>
            decide (first.key = second.key) := by
        simpa [descriptors, datums, matrix, matrixRows] using
          CarrierRankKeyEquality.bits_numericRouteDescriptors
            formula wellFormed degree isLocal forward nonempty
      _ = matrix (datums.zipIdx.map Prod.fst) fun first second =>
            decide (first.key = second.key) := by
        rw [List.zipIdx_map_fst]
      _ = matrix datums.zipIdx fun first second =>
            decide (first.1.key = second.1.key) :=
        matrix_map datums.zipIdx Prod.fst fun first second =>
          decide (first.key = second.key)
  have successorBitsEq :
      successorBits descriptors =
        matrix datums.zipIdx fun first second =>
          decide (CarrierRankGlobal.rankAt datums second =
            CarrierRankGlobal.rankAt datums first + 1) := by
    rw [successorBits_eq_flatMap]
    change matrix (CarrierRankGlobal.ranks descriptors)
        (fun first second => decide (second = first + 1)) = _
    rw [CarrierRankGlobal.ranks_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty]
    change matrix (datums.zipIdx.map (CarrierRankGlobal.rankAt datums))
        (fun first second => decide (second = first + 1)) = _
    exact matrix_map datums.zipIdx (CarrierRankGlobal.rankAt datums)
      fun first second => decide (second = first + 1)
  change SignedUnaryStrictLower.pairwise .conjunction
      (CarrierRankKeyEquality.bits descriptors)
      (successorBits descriptors) = _
  rw [keyBitsEq, successorBitsEq, pairwise_matrix]
  rfl

end CarrierRankGlobalSuccessor
end LeanTrominoes.PeriodicOrthocrossing
