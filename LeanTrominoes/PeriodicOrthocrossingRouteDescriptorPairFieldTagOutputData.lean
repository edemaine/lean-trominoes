/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerFunctionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagControlData

/-! # Raw output of the route-descriptor pair field tagger -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags

/-- Physical tagged-field output for an arbitrary pair-token stream. -/
def tokens (source : List DelimitedBinaryWordPairs.Token) : List Token :=
  LightweightFiniteStateTransducer.output
    .between transition finish source

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags
