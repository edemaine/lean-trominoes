/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler

/-! # Compiler for indexed crossing-segment candidate fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open CarrierCrossingIndexedSegmentField

def crossingIndexedSegmentFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  RouteDescriptorPairAffine.normalizedFields (keepPositive field)
    (crossingIndexedSegmentExpressions field)
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)

def crossingIndexedSegmentFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (crossingIndexedSegmentFields field) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    (RouteDescriptorPairAffine.normalizedFieldsComputableInPolyTime
      (keepPositive field) (crossingIndexedSegmentExpressions field))
  unfold crossingIndexedSegmentFields
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
