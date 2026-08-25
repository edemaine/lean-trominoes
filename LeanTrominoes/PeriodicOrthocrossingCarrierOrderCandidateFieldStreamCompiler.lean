/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalFieldStreamCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # Combined candidate-field stream for carrier order coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateFieldStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalFields (keepPositive : Bool)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  TerminalDirectionalOrderFieldStream.emittedFields keepPositive
    (CarrierKeyRecipeStream.terminalTags input)

def crossingFields (keepPositive : Bool)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CrossingOrderFieldStream.emittedFields keepPositive
    (CarrierKeyRecipeStream.crossingTags input)

def emittedFields (keepPositive : Bool)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  terminalFields keepPositive input ++ crossingFields keepPositive input

/-- Append the zero-valued rejection sentinel expected by representative
lookup. -/
def emittedFieldsWithSentinel (keepPositive : Bool)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  emittedFields keepPositive input ++ [.delimiter]

def terminalFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (terminalFields keepPositive) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalDirectionalOrderFieldStream.emittedFields
      keepPositive (CarrierKeyRecipeStream.terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
    (TerminalDirectionalOrderFieldStream.emittedFieldsComputableInPolyTime
      keepPositive)

def crossingFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (crossingFields keepPositive) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingOrderFieldStream.emittedFields keepPositive
      (CarrierKeyRecipeStream.crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.crossingTagsComputableInPolyTime
    (CrossingOrderFieldStream.emittedFieldsComputableInPolyTime keepPositive)

def emittedFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (emittedFields keepPositive) :=
  TM2ListAppend.computableInPolyTime
    (terminalFieldsComputableInPolyTime keepPositive)
    (crossingFieldsComputableInPolyTime keepPositive)

def emittedFieldsWithSentinelComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (emittedFieldsWithSentinel keepPositive) := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TM2ListAppend.appendFixedWords
      [UnaryFieldEncoderMachine.Symbol.delimiter]
      (emittedFields keepPositive input))
  exact TM2CompositionMachine.computableInPolyTime
    (emittedFieldsComputableInPolyTime keepPositive)
    (TM2ListAppend.appendFixedComputableInPolyTime
      [UnaryFieldEncoderMachine.Symbol.delimiter])

end CarrierOrderCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
