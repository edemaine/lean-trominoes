/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapZipIdxCongr
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRank

/-! # Global streams of retained angular occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Stable terminal ranks of all source occurrences in their single global
presentation order. -/
def retainedOccurrenceGlobalStableTerminalRanks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List Nat :=
  let copies := allOccurrenceVariables source
  copies.zipIdx.map fun entry =>
    StableListRanks.selectedIndexedLowerRank
      (retainedOccurrenceTerminalCoordinate routes)
      (fun other => decide (other.1 = entry.1.1)) copies entry

/-- The indexed global stream is pointwise the previously defined named-copy
global stable rank. -/
theorem retainedOccurrenceGlobalStableTerminalRanks_eq_map
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalStableTerminalRanks source routes =
      (allOccurrenceVariables source).map
        (retainedOccurrenceGlobalStableTerminalRank source routes) := by
  unfold retainedOccurrenceGlobalStableTerminalRanks
  dsimp only
  apply List.map_zipIdx_eq_map_of_mem
  intro entry entryMember
  have indexLt : entry.2 < (allOccurrenceVariables source).length :=
    List.snd_lt_of_mem_zipIdx entryMember
  have valueEq :
      (allOccurrenceVariables source)[entry.2]'indexLt = entry.1 := by
    exact (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp entryMember)).2
  have indexEq :
      (allOccurrenceVariables source).idxOf entry.1 = entry.2 := by
    rw [← valueEq]
    exact (allOccurrenceVariables_nodup source).idxOf_getElem
      entry.2 indexLt
  unfold retainedOccurrenceGlobalStableTerminalRank
  dsimp only
  rw [indexEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
