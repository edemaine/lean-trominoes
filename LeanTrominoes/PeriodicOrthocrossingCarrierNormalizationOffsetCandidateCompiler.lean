/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler

/-! # Candidate compiler for carrier normalization-offset fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open CarrierNormalizationOffsetField

def terminalNormalizationOffsetFields (field : Field)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields (keepPositive field)
    (terminalNormalizationOffsetExpressions field) tokens

def terminalNormalizationOffsetFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (terminalNormalizationOffsetFields field) :=
  normalizedFieldsComputableInPolyTime
    (keepPositive field) (terminalNormalizationOffsetExpressions field)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open CarrierNormalizationOffsetField

def crossingNormalizationOffsetFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  RouteDescriptorPairAffine.normalizedFields (keepPositive field)
    (crossingNormalizationOffsetExpressions field)
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)

def crossingNormalizationOffsetFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (crossingNormalizationOffsetFields field) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    (RouteDescriptorPairAffine.normalizedFieldsComputableInPolyTime
      (keepPositive field) (crossingNormalizationOffsetExpressions field))
  unfold crossingNormalizationOffsetFields
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
