/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyOrderData

/-! # Terminal-prefix presentation of retained carrier-key filtering -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Duplicating each occurrence key does not change membership. -/
@[simp] theorem mem_occurrenceTerminalCarrierKeys_iff
    (occurrences : List (IndexedGridSegment × Cell))
    (key : Nat × Nat × Cell) :
    key ∈ occurrenceTerminalCarrierKeys occurrences ↔
      key ∈ occurrenceCarrierKeys occurrences := by
  unfold occurrenceTerminalCarrierKeys occurrenceCarrierKeys
  simp [eq_comm]

/-- The final base-key filter can equivalently test membership in the
duplicated terminal prefix itself. -/
theorem retainedCarrierKeysOfOccurrencesAndPairs_eq_terminalPrefixFilter
    (occurrences : List (IndexedGridSegment × Cell))
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) :
    retainedCarrierKeysOfOccurrencesAndPairs occurrences pairs =
      (occurrenceTerminalCarrierKeys occurrences ++
          occurrencePairCarrierKeyScan pairs).dedup.filter fun key =>
        key ∈ occurrenceTerminalCarrierKeys occurrences := by
  unfold retainedCarrierKeysOfOccurrencesAndPairs
  apply List.filter_congr
  intro key _keyMember
  exact Bool.decide_congr
    (mem_occurrenceTerminalCarrierKeys_iff occurrences key).symm

end LeanTrominoes.PeriodicOrthocrossing
