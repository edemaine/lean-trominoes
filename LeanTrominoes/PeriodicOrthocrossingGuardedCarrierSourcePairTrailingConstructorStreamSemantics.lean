/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterData
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorNodeSemantics

/-! # Stream semantics of delayed carrier constructor classification -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

theorem scan_nodesAtPeriod (period : Nat) (nodes : List CarrierNode) :
    FiniteStateTransducer.scan transition .between
        (DelimitedBinaryWords.encode
          (CarrierSourcePairFieldFormatter.words
            (nodes.map
              (CarrierNodeNormalizedSourceKeys.pairAtPeriod period)))) =
      (.between,
        DelimitedBinaryWords.encode (nodeWordsAtPeriod period nodes)) := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction =>
      unfold CarrierSourcePairFieldFormatter.words
        nodeWordsAtPeriod DelimitedBinaryWords.encode at induction ⊢
      simp only [List.map_cons, List.flatMap_cons]
      rw [FiniteStateTransducer.scan_append, scan_nodeAtPeriod]
      dsimp
      rw [induction]

/-- The physical finite-state pass classifies every normalized carrier pair
independently without disturbing its global stream order. -/
theorem tokens_nodesAtPeriod (period : Nat) (nodes : List CarrierNode) :
    tokens
        (DelimitedBinaryWords.encode
          (CarrierSourcePairFieldFormatter.words
            (nodes.map
              (CarrierNodeNormalizedSourceKeys.pairAtPeriod period)))) =
      DelimitedBinaryWords.encode (nodeWordsAtPeriod period nodes) := by
  simp [tokens, FiniteStateTransducer.output,
    scan_nodesAtPeriod, finish]

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing
