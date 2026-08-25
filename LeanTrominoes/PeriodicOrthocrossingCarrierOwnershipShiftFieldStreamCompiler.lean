/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Pair-stream compilers for carrier ownership-shift fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

namespace TerminalOwnershipShiftFieldStream

open Computability Turing
open CarrierOwnershipShiftField

def blockFields (field : Field)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorPairAffine.terminalOwnershipShiftFields field tokens)

def blockFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (blockFields field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorPairAffine.terminalOwnershipShiftFieldsComputableInPolyTime
      field)
    (fun _ => rfl)

def emittedFields (field : Field)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    (blockFields field) tokens

def emittedFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (emittedFields field) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (blockFieldsComputableInPolyTime field)
    RouteDescriptorPairFieldTags.isPairEnd

end TerminalOwnershipShiftFieldStream

namespace CrossingOwnershipShiftFieldStream

open Computability Turing
open CarrierOwnershipShiftField

def blockFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftFields
      field tokens)

def blockFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (blockFields field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorOccurrenceSlotCrossing.crossingOwnershipShiftFieldsComputableInPolyTime
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

end CrossingOwnershipShiftFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
