/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankCountData

/-! # Semantics of global retained occurrence stable-rank counts -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

private theorem count_true_map_eq_filter_length
    {Value : Type*} (values : List Value) (predicate : Value → Bool) :
    (values.map predicate).count true =
      (values.filter predicate).length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases selected : predicate value <;>
        simp [selected, induction]

/-- The two comparison-row counts at one genuine indexed occurrence are
exactly its selected stable lower rank in the global presentation. -/
theorem retainedOccurrenceGlobalStableTerminalRankCountAt_eq
    {Variable : Type*} [DecidableEq Variable]
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copies : List (ThreeOccurrenceVariable Variable))
    (entry : ThreeOccurrenceVariable Variable × Nat)
    (entryMember : entry ∈ copies.zipIdx) :
    retainedOccurrenceGlobalStableTerminalRankCountAt
        routes copies entry =
      StableListRanks.selectedIndexedLowerRank
        (retainedOccurrenceTerminalCoordinate routes)
        (fun other => decide (other.1 = entry.1.1)) copies entry := by
  have lookup : copies[entry.2]? = some entry.1 :=
    (List.mem_zipIdx_iff_getElem?).mp entryMember
  have semantic :=
    StableListRanks.selectedIndexedLowerRank_eq
      (retainedOccurrenceTerminalCoordinate routes)
      (fun other : ThreeOccurrenceVariable Variable =>
        decide (other.1 = entry.1.1))
      copies entry.2 entry.1 lookup
  have lowerCount :
      (copies.map
          (retainedOccurrenceGlobalStableLowerPredicate
            routes entry.1)).count true =
        (copies.filter fun other =>
          decide (other.1 = entry.1.1) &&
            decide
              (retainedOccurrenceTerminalCoordinate routes other <
                retainedOccurrenceTerminalCoordinate routes entry.1)).length := by
    rw [count_true_map_eq_filter_length]
    rfl
  have tieCount :
      ((copies.map
          (retainedOccurrenceGlobalStableTiePredicate
            routes entry.1)).take entry.2).count true =
        ((copies.take entry.2).filter fun other =>
          decide (other.1 = entry.1.1) &&
            decide
              (retainedOccurrenceTerminalCoordinate routes other =
                retainedOccurrenceTerminalCoordinate routes entry.1)).length := by
    rw [← List.map_take, count_true_map_eq_filter_length]
    rfl
  unfold retainedOccurrenceGlobalStableTerminalRankCountAt
  rw [lowerCount, tieCount]
  exact semantic.symm

/-- The complete count-computed stream is exactly the semantic global stable
rank stream. -/
theorem retainedOccurrenceGlobalStableTerminalRankCounts_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableTerminalRankCounts source routes =
      retainedOccurrenceGlobalStableTerminalRanks source routes := by
  unfold retainedOccurrenceGlobalStableTerminalRankCounts
    retainedOccurrenceGlobalStableTerminalRanks
  dsimp only
  apply List.map_congr_left
  intro entry entryMember
  exact retainedOccurrenceGlobalStableTerminalRankCountAt_eq
    routes (allOccurrenceVariables source) entry entryMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
