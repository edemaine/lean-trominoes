/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerFunctionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagControlData

/-! # Finite-state machine data for route-descriptor pair tags -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Physical tagged-field output for an arbitrary pair-token stream. -/
def tokens (source : List DelimitedBinaryWordPairs.Token) : List Token :=
  FiniteStateTransducer.output .between transition finish source

/-- Tagged output presented at the semantic pair-list input boundary. -/
def inputTokens (input : DelimitedBinaryWordPairs.Input) : List Token :=
  tokens (DelimitedBinaryWordPairs.encode input)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags
