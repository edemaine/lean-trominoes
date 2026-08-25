/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerPredicateData
import LeanTrominoes.StableListIndexedLowerRankSemantics

/-! # Semantic stable lower ranks of carrier data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

/-- Strict lower rank in the same carrier-key fiber, with the original global
presentation indices providing the stable coordinate tie-breaker. -/
def stableRankAt (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat) : Nat :=
  StableListRanks.selectedIndexedLowerRank
    CarrierNodeRankDatum.orderCoordinate
    (fun other => decide (entry.1.key = other.key)) datums entry

private theorem count_true_map_eq_filter_length
    {Value : Type*} (values : List Value) (predicate : Value → Bool) :
    (values.map predicate).count true =
      (values.filter predicate).length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases selected : predicate value <;>
        simp [selected, induction]

/-- The compiled strict-lower plus earlier-tie count is exactly the strict
lexicographic lower rank in the selected carrier-key fiber. -/
theorem rankAt_eq_stableRankAt
    (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat)
    (member : entry ∈ datums.zipIdx) :
    rankAt datums entry = stableRankAt datums entry := by
  have lookup : datums[entry.2]? = some entry.1 :=
    (List.mem_zipIdx_iff_getElem?).mp member
  have semantic := StableListRanks.selectedIndexedLowerRank_eq
    CarrierNodeRankDatum.orderCoordinate
    (fun other : CarrierNodeRankDatum =>
      decide (entry.1.key = other.key))
    datums entry.2 entry.1 lookup
  have lowerCount :
      (datums.map (lowerPredicate entry.1)).count true =
        (datums.filter fun other =>
          decide (entry.1.key = other.key) &&
            decide
              (other.orderCoordinate < entry.1.orderCoordinate)).length := by
    rw [count_true_map_eq_filter_length]
    rfl
  have tieCount :
      ((datums.map (tiePredicate entry.1)).take entry.2).count true =
        ((datums.take entry.2).filter fun other =>
          decide (entry.1.key = other.key) &&
            decide
              (other.orderCoordinate = entry.1.orderCoordinate)).length := by
    rw [← List.map_take, count_true_map_eq_filter_length]
    apply congrArg List.length
    apply List.filter_congr
    intro other _otherMember
    unfold tiePredicate
    rw [show decide
        (entry.1.orderCoordinate = other.orderCoordinate) =
        decide (other.orderCoordinate = entry.1.orderCoordinate) by
      simp [eq_comm]]
  unfold rankAt stableRankAt
  rw [lowerCount, tieCount]
  exact semantic.symm

/-- Pointwise replacement of the implementation counts by semantic stable
fiber ranks over the complete indexed presentation. -/
theorem map_rankAt_eq_stableRankAt
    (datums : List CarrierNodeRankDatum) :
    datums.zipIdx.map (rankAt datums) =
      datums.zipIdx.map (stableRankAt datums) := by
  apply List.map_congr_left
  intro entry member
  exact rankAt_eq_stableRankAt datums entry member

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
