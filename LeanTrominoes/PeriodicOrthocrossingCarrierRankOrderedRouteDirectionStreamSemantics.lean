/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteDirectionStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoderSemantics

/-! # Semantics of rank-ordered retained carrier route directions -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- The composite stream decodes every tagged matrix field in its original
row-major order. -/
theorem retainedRouteDirectionStream_eq_flatMap
    (descriptors : List RouteDescriptor) :
    retainedRouteDirectionStream descriptors =
      (taggedSpanCodes descriptors).flatMap fun code =>
        CarrierTaggedSpanRouteDirections.blockOutput
          (UnaryFieldEncoderMachine.unaryField code) := by
  unfold retainedRouteDirectionStream
  exact CarrierTaggedSpanRouteDirections.stream_unaryFields _

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
