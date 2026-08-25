/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresencePipelineCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # Complete candidate streams for indexed crossing-segment fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingIndexedSegmentCandidateFieldStream

open Computability Turing
open CarrierCrossingIndexedSegmentField

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalFields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierBoundaryPresencePipeline.terminalFields input

def crossingFields (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CrossingIndexedSegmentFieldStream.emittedFields field
    (CarrierKeyRecipeStream.crossingTags input)

def emittedFields (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  terminalFields input ++ crossingFields field input

def emittedFieldsWithSentinel (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  emittedFields field input ++ [.delimiter]

def terminalFieldsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalFields :=
  CarrierBoundaryPresencePipeline.terminalFieldsComputableInPolyTime

def crossingFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (crossingFields field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingIndexedSegmentFieldStream.emittedFields field
      (CarrierKeyRecipeStream.crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.crossingTagsComputableInPolyTime
    (CrossingIndexedSegmentFieldStream.emittedFieldsComputableInPolyTime field)

def emittedFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (emittedFields field) :=
  TM2ListAppend.computableInPolyTime
    terminalFieldsComputableInPolyTime
    (crossingFieldsComputableInPolyTime field)

def emittedFieldsWithSentinelComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (emittedFieldsWithSentinel field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TM2ListAppend.appendFixedWords
      [UnaryFieldEncoderMachine.Symbol.delimiter]
      (emittedFields field input))
  exact TM2CompositionMachine.computableInPolyTime
    (emittedFieldsComputableInPolyTime field)
    (TM2ListAppend.appendFixedComputableInPolyTime
      [UnaryFieldEncoderMachine.Symbol.delimiter])

end CarrierCrossingIndexedSegmentCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
