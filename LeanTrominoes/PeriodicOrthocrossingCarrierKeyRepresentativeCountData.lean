/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowData

/-! # Occurrence counts of retained carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Number of active terminal or crossing-boundary candidates on every
retained carrier key, in last-occurrence representative order. -/
def paddedCarrierKeyRepresentativeCounts
    (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (paddedCarrierKeyRepresentativeRows descriptors)

end LeanTrominoes.PeriodicOrthocrossing
