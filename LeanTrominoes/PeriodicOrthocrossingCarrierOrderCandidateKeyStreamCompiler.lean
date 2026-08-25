/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalKeyStreamCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Combined candidate-key stream for carrier order coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateKeyStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  TerminalDirectionalCarrierKeyStream.emittedStream
    (CarrierKeyRecipeStream.terminalTags input)

def crossingTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeStream.crossingTokens input

def emittedTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  terminalTokens input ++ crossingTokens input

def terminalTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalDirectionalCarrierKeyStream.emittedStream
      (CarrierKeyRecipeStream.terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
    TerminalDirectionalCarrierKeyStream.emittedStreamComputableInPolyTime

def crossingTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingTokens :=
  CarrierKeyRecipeStream.crossingTokensComputableInPolyTime

def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      emittedTokens :=
  TM2ListAppend.computableInPolyTime
    terminalTokensComputableInPolyTime
    crossingTokensComputableInPolyTime

end CarrierOrderCandidateKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
