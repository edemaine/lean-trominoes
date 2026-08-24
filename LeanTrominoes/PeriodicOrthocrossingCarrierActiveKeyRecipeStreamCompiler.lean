/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeStreamCompiler

/-! # Complete activity-supported carrier-key recipe stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyRecipeStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  TerminalActiveCarrierKeyRecipeStream.emittedStream
    (CarrierKeyRecipeStream.terminalTags input)

def crossingTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CrossingActiveCarrierKeyRecipeStream.emittedStream
    (CarrierKeyRecipeStream.crossingTags input)

def emittedTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  terminalTokens input ++ crossingTokens input

noncomputable def terminalTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalActiveCarrierKeyRecipeStream.emittedStream
      (CarrierKeyRecipeStream.terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
    TerminalActiveCarrierKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def crossingTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingActiveCarrierKeyRecipeStream.emittedStream
      (CarrierKeyRecipeStream.crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.crossingTagsComputableInPolyTime
    CrossingActiveCarrierKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      emittedTokens :=
  TM2ListAppend.computableInPolyTime
    terminalTokensComputableInPolyTime crossingTokensComputableInPolyTime

end CarrierActiveKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
