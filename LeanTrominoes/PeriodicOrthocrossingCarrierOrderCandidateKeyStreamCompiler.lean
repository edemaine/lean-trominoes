/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Full source-identity keys for carrier order coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateKeyStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalComponentTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  TerminalDirectionalSourceKeyStream.emittedStream
    (CarrierKeyRecipeStream.terminalTags input)

def crossingComponentTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CrossingSourceKeyRecipeStream.emittedStream
    (CarrierKeyRecipeStream.crossingTags input)

def componentTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  terminalComponentTokens input ++ crossingComponentTokens input

def emittedTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordGuardedPairMerge.tokens (componentTokens input)

def terminalComponentTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalComponentTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalDirectionalSourceKeyStream.emittedStream
      (CarrierKeyRecipeStream.terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
    TerminalDirectionalSourceKeyStream.emittedStreamComputableInPolyTime

def crossingComponentTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingComponentTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingSourceKeyRecipeStream.emittedStream
      (CarrierKeyRecipeStream.crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.crossingTagsComputableInPolyTime
    CrossingSourceKeyRecipeStream.emittedStreamComputableInPolyTime

def componentTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      componentTokens :=
  TM2ListAppend.computableInPolyTime
    terminalComponentTokensComputableInPolyTime
    crossingComponentTokensComputableInPolyTime

def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      emittedTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => DelimitedBinaryWordGuardedPairMerge.tokens
      (componentTokens input))
  exact TM2CompositionMachine.computableInPolyTime
    componentTokensComputableInPolyTime
    DelimitedBinaryWordGuardedPairMerge.tokensComputableInPolyTime

end CarrierOrderCandidateKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
