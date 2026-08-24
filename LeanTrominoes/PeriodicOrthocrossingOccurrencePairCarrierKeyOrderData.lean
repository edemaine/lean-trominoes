/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyData

/-! # Graph-free retained carrier-key order -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Carrier keys of an arbitrary ordered occurrence stream. -/
def occurrenceCarrierKeys
    (occurrences : List (IndexedGridSegment × Cell)) :
    List (Nat × Nat × Cell) :=
  occurrences.map occurrenceCarrierKey

/-- Two adjacent terminal-key copies for every occurrence. -/
def occurrenceTerminalCarrierKeys
    (occurrences : List (IndexedGridSegment × Cell)) :
    List (Nat × Nat × Cell) :=
  occurrences.flatMap fun occurrence =>
    [occurrenceCarrierKey occurrence, occurrenceCarrierKey occurrence]

/-- Exact last-occurrence key order determined only by neighboring
occurrences and accepted crossing pairs. -/
def retainedCarrierKeysOfOccurrencesAndPairs
    (occurrences : List (IndexedGridSegment × Cell))
    (pairs : List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))) : List (Nat × Nat × Cell) :=
  (occurrenceTerminalCarrierKeys occurrences ++
      occurrencePairCarrierKeyScan pairs).dedup.filter fun key =>
    key ∈ occurrenceCarrierKeys occurrences

end LeanTrominoes.PeriodicOrthocrossing
