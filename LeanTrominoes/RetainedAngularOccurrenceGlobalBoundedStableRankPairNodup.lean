/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitPortAssignment
import LeanTrominoes.RetainedAngularFanBoundaryRouteFamily
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankPairNodup

/-! # Uniqueness after bounding global stable ranks to eight slots -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- A genuine global occurrence's stable rank is below its semantic atom's
total occurrence count. -/
theorem retainedOccurrenceGlobalStableTerminalRank_lt_count
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ allOccurrenceVariables source) :
    retainedOccurrenceGlobalStableTerminalRank source routes copy <
      source.variableOccurrences.count copy.1 := by
  let fiber := occurrenceVariables source copy.1
  let ordered := StableListRanks.valuesByStableLowerRank
    (retainedOccurrenceTerminalCoordinate routes) fiber
  have fiberMember : copy ∈ fiber := by
    dsimp [fiber]
    rw [occurrenceVariables_eq_filter]
    simp [copyMember]
  have rankEq :
      retainedOccurrenceGlobalStableTerminalRank source routes copy =
        ordered.idxOf copy := by
    calc
      _ = retainedOccurrenceStableTerminalRank
          source routes copy.1 copy :=
        (retainedOccurrenceStableTerminalRank_eq_global
          source routes copy.1 copy fiberMember).symm
      _ = ordered.idxOf copy := by
        exact StableListRanks.selectedIndexedLowerRank_true_eq_idxOf_valuesByStableLowerRank
          (retainedOccurrenceTerminalCoordinate routes)
          fiber (occurrenceVariables_nodup source copy.1)
          copy fiberMember
  have orderedMember : copy ∈ ordered := by
    dsimp [ordered]
    rw [StableListRanks.valuesByStableLowerRank_eq_insertionSort]
    exact (List.mem_insertionSort
      (r := fun first second : ThreeOccurrenceVariable Variable =>
        retainedOccurrenceTerminalCoordinate routes first <=
          retainedOccurrenceTerminalCoordinate routes second)).mpr fiberMember
  rw [rankEq, ← occurrenceVariables_length]
  have rankLt := List.idxOf_lt_length_of_mem orderedMember
  simpa [ordered, StableListRanks.valuesByStableLowerRank_eq_insertionSort]
    using rankLt

/-- Semantic atom and bounded eight-slot rank at every global occurrence. -/
def retainedOccurrenceGlobalBoundedStableAtomRankPairs
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    List (Variable × Nat) :=
  (allOccurrenceVariables source).map fun copy =>
    (copy.1,
      (boundedRetainedTerminalSlot
        (retainedOccurrenceGlobalStableTerminalRank
          source routes copy)).val)

/-- With at most eight occurrences per atom, bounding stable ranks is
lossless, so the bounded atom/rank pairs remain duplicate-free. -/
theorem retainedOccurrenceGlobalBoundedStableAtomRankPairs_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (occurrences : source.OccurrencesAtMost 8) :
    (retainedOccurrenceGlobalBoundedStableAtomRankPairs
      source routes).Nodup := by
  have pairEq :
      retainedOccurrenceGlobalBoundedStableAtomRankPairs source routes =
        retainedOccurrenceGlobalStableAtomRankPairs source routes := by
    unfold retainedOccurrenceGlobalBoundedStableAtomRankPairs
      retainedOccurrenceGlobalStableAtomRankPairs
    apply List.map_congr_left
    intro copy copyMember
    congr 1
    apply boundedRetainedTerminalSlot_val_of_lt
    exact (retainedOccurrenceGlobalStableTerminalRank_lt_count
      source routes copy copyMember).trans_le (occurrences copy.1)
  rw [pairEq]
  exact retainedOccurrenceGlobalStableAtomRankPairs_nodup source routes

end PeriodicEightOccurrenceSplit
end LeanTrominoes
