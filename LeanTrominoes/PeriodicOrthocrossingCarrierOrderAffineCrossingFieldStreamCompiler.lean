/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Slot-pair-stream compiler for crossing order-coordinate fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingOrderFieldStream

open Computability Turing

def blockFields (keepPositive : Bool)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields
      keepPositive tokens)

def blockFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime id id (blockFields keepPositive) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorOccurrenceSlotCrossing.crossingOrderFieldsComputableInPolyTime
      keepPositive)
    (fun _ => rfl)

def emittedFields (keepPositive : Bool)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    (blockFields keepPositive) tokens

def emittedFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime id id (emittedFields keepPositive) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (blockFieldsComputableInPolyTime keepPositive)
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

end CrossingOrderFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
