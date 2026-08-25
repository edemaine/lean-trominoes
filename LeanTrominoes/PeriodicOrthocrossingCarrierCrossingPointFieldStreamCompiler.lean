/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Slot-pair stream compiler for crossing-point fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingPointFieldStream

open Computability Turing
open CarrierCrossingPointField

def blockFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorOccurrenceSlotCrossing.crossingPointFields field tokens)

def blockFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (blockFields field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorOccurrenceSlotCrossing.crossingPointFieldsComputableInPolyTime
      field)
    (fun _ => rfl)

def emittedFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    (blockFields field) tokens

def emittedFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (emittedFields field) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (blockFieldsComputableInPolyTime field)
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

end CrossingPointFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
