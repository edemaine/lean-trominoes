/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerFunctionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagControlData

/-! # Finite-state machine data for occurrence-slot pair tags -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

/-- Physical twelve-field tagged output for an arbitrary pair-token stream. -/
def tokens (source : List DelimitedBinaryWordPairs.Token) : List Token :=
  FiniteStateTransducer.output .between transition finish source

/-- Twelve-field tags at the semantic pair-list input boundary. -/
def inputTokens (input : DelimitedBinaryWordPairs.Input) : List Token :=
  tokens (DelimitedBinaryWordPairs.encode input)

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
