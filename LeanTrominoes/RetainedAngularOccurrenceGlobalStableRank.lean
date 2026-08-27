/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilterTakeIdxOf
import LeanTrominoes.RetainedAngularOccurrenceStableRankCounts

/-! # Global-stream retained angular occurrence stable ranks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Stable terminal rank computed in the single global occurrence
presentation, selecting only entries belonging to the target atom. -/
def retainedOccurrenceGlobalStableTerminalRank
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable) : Nat :=
  let copies := allOccurrenceVariables source
  StableListRanks.selectedIndexedLowerRank
    (retainedOccurrenceTerminalCoordinate routes)
    (fun other => decide (other.1 = copy.1)) copies
    (copy, copies.idxOf copy)

/-- For a genuine occurrence, selecting its atom inside the one global
presentation gives the same stable rank as ranking in its per-atom
occurrence fiber. -/
theorem retainedOccurrenceStableTerminalRank_eq_global
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    retainedOccurrenceStableTerminalRank source routes atom copy =
      retainedOccurrenceGlobalStableTerminalRank source routes copy := by
  have copyAtom : copy.1 = atom :=
    occurrenceVariables_fst source atom copyMember
  subst atom
  have copyGlobal : copy ∈ allOccurrenceVariables source := by
    rw [occurrenceVariables_eq_filter] at copyMember
    exact (List.mem_filter.mp copyMember).1
  have globalCounts :=
    StableListRanks.selectedIndexedLowerRank_eq
      (retainedOccurrenceTerminalCoordinate routes)
      (fun other : ThreeOccurrenceVariable Variable =>
        decide (other.1 = copy.1))
      (allOccurrenceVariables source)
      ((allOccurrenceVariables source).idxOf copy) copy
      (List.getElem?_idxOf copyGlobal)
  rw [retainedOccurrenceStableTerminalRank_eq_counts
    source routes copy.1 copy copyMember]
  unfold retainedOccurrenceGlobalStableTerminalRank
  rw [globalCounts]
  rw [occurrenceVariables_eq_filter]
  rw [List.take_idxOf_filter_eq_filter_take_idxOf
    (fun other : ThreeOccurrenceVariable Variable =>
      decide (other.1 = copy.1))
    (allOccurrenceVariables source) copy copyGlobal (by simp)]
  simp only [List.filter_filter, Bool.and_comm]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
