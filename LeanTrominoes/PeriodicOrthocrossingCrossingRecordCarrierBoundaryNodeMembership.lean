/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeData

/-! # Membership in reconstructed boundary-node blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

theorem mem_flatMap_crossingRecordCarrierBoundaryNodes_iff
    (records : List CrossingRecord) (node : CarrierNode) :
    node ∈ records.flatMap crossingRecordCarrierBoundaryNodes ↔
      ∃ record ∈ records,
        node = CarrierNode.boundary ⟨record, .left⟩ ∨
          node = CarrierNode.boundary ⟨record, .right⟩ ∨
          node = CarrierNode.boundary ⟨record, .top⟩ ∨
          node = CarrierNode.boundary ⟨record, .bottom⟩ := by
  simp [crossingRecordCarrierBoundaryNodes]

end LeanTrominoes.PeriodicOrthocrossing
