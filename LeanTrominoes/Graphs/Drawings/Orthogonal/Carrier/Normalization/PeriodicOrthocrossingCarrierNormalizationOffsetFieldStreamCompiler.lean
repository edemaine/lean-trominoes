/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Normalization.PeriodicOrthocrossingCarrierNormalizationOffsetCandidateCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.Computation.TM2.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.Computation.TM2.TM2PolyTimeOutputEncodingTransport

/-! # Pair-stream compilers for carrier normalization-offset fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

namespace TerminalNormalizationOffsetFieldStream

open Computability Turing
open CarrierNormalizationOffsetField

def blockFields (field : Field)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorPairAffine.terminalNormalizationOffsetFields field tokens)

def blockFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (blockFields field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorPairAffine.terminalNormalizationOffsetFieldsComputableInPolyTime
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

end TerminalNormalizationOffsetFieldStream

namespace CrossingNormalizationOffsetFieldStream

open Computability Turing
open CarrierNormalizationOffsetField

def blockFields (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetFields
      field tokens)

def blockFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime id id (blockFields field) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorOccurrenceSlotCrossing.crossingNormalizationOffsetFieldsComputableInPolyTime
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

end CrossingNormalizationOffsetFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
