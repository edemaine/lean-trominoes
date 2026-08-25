/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler

/-! # Candidate compiler for carrier ownership-shift fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open CarrierOwnershipShiftField

def terminalOwnershipShiftFields (field : Field)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields (keepPositive field)
    (terminalOwnershipShiftExpressions field) tokens

def terminalOwnershipShiftFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (terminalOwnershipShiftFields field) :=
  normalizedFieldsComputableInPolyTime
    (keepPositive field) (terminalOwnershipShiftExpressions field)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open Computability Turing
open CarrierOwnershipShiftField

def crossingOwnershipShiftFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Nat :=
  RouteDescriptorPairAffine.normalizedFields (keepPositive field)
    (crossingOwnershipShiftExpressions field)
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)

def crossingOwnershipShiftFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (crossingOwnershipShiftFields field) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    (RouteDescriptorPairAffine.normalizedFieldsComputableInPolyTime
      (keepPositive field) (crossingOwnershipShiftExpressions field))
  unfold crossingOwnershipShiftFields
  exact composed

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
