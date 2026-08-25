/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCandidateExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler

/-! # Compiler for crossing order-coordinate candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing

/-- Normalize every affine crossing order-coordinate candidate after
projecting away the occurrence-slot fields. -/
def crossingOrderFields (keepPositive : Bool)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  RouteDescriptorPairAffine.normalizedFields keepPositive
    crossingOrderExpressions
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)

def crossingOrderFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (crossingOrderFields keepPositive) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    (RouteDescriptorPairAffine.normalizedFieldsComputableInPolyTime
      keepPositive crossingOrderExpressions)
  unfold crossingOrderFields
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
