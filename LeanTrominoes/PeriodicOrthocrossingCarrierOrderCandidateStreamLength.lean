/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeOutputSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateKeySentinelCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCrossingSourceKeyLength
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderTerminalSourceKeyLength

/-! # Length alignment of carrier order-coordinate candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateFieldStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- The combined source-identity component stream has exactly two words per
positive or negative order-coordinate value. -/
theorem componentWords_length_twice_values (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    (CarrierOrderCandidateKeyStream.componentWords descriptors).length =
      2 * (values keepPositive descriptors).length := by
  unfold CarrierOrderCandidateKeyStream.componentWords values
  rw [List.length_append, List.length_append,
    TerminalDirectionalSourceKeyStream.guardedComponentWords_length_twice_orderFields
      keepPositive,
    CrossingSourceKeyRecipeStream.guardedWords_length_twice_orderFields
      keepPositive descriptors]
  omega

/-- Merging each adjacent source-key component pair leaves one full compact
identity word for every order-coordinate value. -/
theorem values_length (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    (values keepPositive descriptors).length =
      (CarrierOrderCandidateKeyStream.guardedWords descriptors).length := by
  unfold CarrierOrderCandidateKeyStream.guardedWords
  symm
  exact
    DelimitedBinaryWordGuardedPairMerge.mergeWords_length_of_length_eq_twice
      (CarrierOrderCandidateKeyStream.componentWords descriptors)
      (values keepPositive descriptors).length
      (componentWords_length_twice_values keepPositive descriptors)

/-- Appending the zero sentinel aligns the values with the rejection-sentinel
key appended before representative selection. -/
theorem valuesWithSentinel_length (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    (valuesWithSentinel keepPositive descriptors).length =
      (CarrierOrderCandidateKeyStream.wordsWithSentinel descriptors).words.length := by
  simp [valuesWithSentinel, CarrierOrderCandidateKeyStream.wordsWithSentinel,
    values_length]

end CarrierOrderCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
