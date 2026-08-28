/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorPairSemantics

/-! # Exact carrier-node semantics of delayed constructor classification -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

open DelimitedBinaryWords

theorem scan_carrierNode (node : CarrierNode) :
    FiniteStateTransducer.scan transition .between
        (wordTokens (true :: CarrierNodeSourceKeys.word
          (CarrierNodeSourceKeys.pair node))) =
      (.between, wordTokens
        (match node with
        | .terminal terminal =>
            CarrierKeyWords.word
              (CarrierNodeSourceKeys.pair (.terminal terminal)).1 ++
                [false]
        | .boundary boundary =>
            CarrierNodeSourceKeys.word
              (CarrierNodeSourceKeys.pair (.boundary boundary)) ++
                [true])) := by
  cases node with
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      have scanned := scan_guardedTaggedPair
        (SegmentTerminal.carrierKey ⟨indexed, translate, endpoint⟩)
        (CarrierNodeSourceKeys.taggedKey
          (SegmentTerminal.carrierKey ⟨indexed, translate, endpoint⟩)
          (CarrierNodeSourceKeys.segmentEndTag endpoint))
        (CarrierNodeSourceKeys.segmentEndTag endpoint)
      cases endpoint <;>
        simpa [CarrierNodeSourceKeys.pair,
          CarrierNodeSourceKeys.segmentEndTag,
          TagRemainder.advance, TagRemainder.next,
          TagRemainder.isBoundary] using scanned
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      have scanned := scan_guardedTaggedPair
        (CarrierNodeSourceKeys.firstCrossingKey ⟨crossing, side⟩)
        (CarrierNodeSourceKeys.secondCrossingKey ⟨crossing, side⟩)
        (CarrierNodeSourceKeys.crossingSideTag side)
      cases side <;>
        simpa [CarrierNodeSourceKeys.pair,
          CarrierNodeSourceKeys.crossingSideTag,
          TagRemainder.advance, TagRemainder.next,
          TagRemainder.isBoundary] using scanned

/-- The classifier produces the exact delayed-constructor word of every
normalized physical carrier node. -/
theorem scan_nodeAtPeriod (period : Nat) (node : CarrierNode) :
    FiniteStateTransducer.scan transition .between
        (wordTokens (true :: CarrierNodeSourceKeys.word
          (CarrierNodeNormalizedSourceKeys.pairAtPeriod period node))) =
      (.between, wordTokens (nodeWordAtPeriod period node)) := by
  cases node with
  | terminal terminal =>
      simpa [CarrierNodeNormalizedSourceKeys.pairAtPeriod,
        nodeWordAtPeriod, CarrierNodeNormalizedSourceKeys.nodeAtPeriod] using
        scan_carrierNode
          (CarrierNodeNormalizedSourceKeys.nodeAtPeriod period
            (.terminal terminal))
  | boundary boundary =>
      simpa [CarrierNodeNormalizedSourceKeys.pairAtPeriod,
        nodeWordAtPeriod, CarrierNodeNormalizedSourceKeys.nodeAtPeriod] using
        scan_carrierNode
          (CarrierNodeNormalizedSourceKeys.nodeAtPeriod period
            (.boundary boundary))

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing
