/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldStreamCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # Complete candidate streams for carrier normalization-offset fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizationOffsetCandidateFieldStream

open Computability Turing
open CarrierNormalizationOffsetField

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalFields (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  TerminalNormalizationOffsetFieldStream.emittedFields field
    (CarrierKeyRecipeStream.terminalTags input)

def crossingFields (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CrossingNormalizationOffsetFieldStream.emittedFields field
    (CarrierKeyRecipeStream.crossingTags input)

def emittedFields (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  terminalFields field input ++ crossingFields field input

def emittedFieldsWithSentinel (field : Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  emittedFields field input ++ [.delimiter]

def terminalFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (terminalFields field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalNormalizationOffsetFieldStream.emittedFields field
      (CarrierKeyRecipeStream.terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
    (TerminalNormalizationOffsetFieldStream.emittedFieldsComputableInPolyTime
      field)

def crossingFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (crossingFields field) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingNormalizationOffsetFieldStream.emittedFields field
      (CarrierKeyRecipeStream.crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.crossingTagsComputableInPolyTime
    (CrossingNormalizationOffsetFieldStream.emittedFieldsComputableInPolyTime
      field)

def emittedFieldsComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (emittedFields field) :=
  TM2ListAppend.computableInPolyTime
    (terminalFieldsComputableInPolyTime field)
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

end CarrierNormalizationOffsetCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
