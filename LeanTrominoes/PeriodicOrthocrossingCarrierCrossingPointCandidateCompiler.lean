/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler

/-! # Compiler for crossing-point candidate fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open CarrierCrossingPointField

def crossingPointFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  RouteDescriptorPairAffine.normalizedFields (keepPositive field)
    (crossingPointExpressions field)
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)

def crossingPointFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (crossingPointFields field) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    (RouteDescriptorPairAffine.normalizedFieldsComputableInPolyTime
      (keepPositive field) (crossingPointExpressions field))
  unfold crossingPointFields
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
