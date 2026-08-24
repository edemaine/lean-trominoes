/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeData

/-! # Membership in reconstructed terminal-node blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem mem_flatMap_occurrenceCarrierTerminalNodes_iff
    (occurrences : List (IndexedGridSegment × Cell))
    (node : CarrierNode) :
    node ∈ occurrences.flatMap occurrenceCarrierTerminalNodes ↔
      ∃ occurrence ∈ occurrences,
        node = CarrierNode.terminal
            ⟨occurrence.1, occurrence.2, .start⟩ ∨
          node = CarrierNode.terminal
            ⟨occurrence.1, occurrence.2, .finish⟩ := by
  simp [occurrenceCarrierTerminalNodes, occurrenceTerminals]

end LeanTrominoes.PeriodicOrthocrossing
