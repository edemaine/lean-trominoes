/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Complete doubled source-key component stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalTags (input : DelimitedBinaryWords.Input) :
    List RouteDescriptorPairFieldTags.Token :=
  RouteDescriptorPairFieldTags.inputTokens
    (DelimitedBinaryWordPairProductMachine.pairs input)

def crossingTags (input : DelimitedBinaryWords.Input) :
    List RouteDescriptorOccurrenceSlotPairFieldTags.Token :=
  RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
    (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input)

def terminalTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  TerminalSourceKeyRecipeStream.emittedStream (terminalTags input)

def crossingTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CrossingSourceKeyRecipeStream.emittedStream (crossingTags input)

def tokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  terminalTokens input ++ crossingTokens input

noncomputable def terminalTagsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalTags := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => RouteDescriptorPairFieldTags.inputTokens
      (DelimitedBinaryWordPairProductMachine.pairs input))
  exact TM2CompositionMachine.computableInPolyTime
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
    RouteDescriptorPairFieldTags.inputTokensComputableInPolyTime

noncomputable def crossingTagsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingTags := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
      (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input))
  exact TM2CompositionMachine.computableInPolyTime
    DelimitedBinaryWordOccurrenceSlotTags.expandedPairsComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokensComputableInPolyTime

noncomputable def terminalTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      terminalTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => TerminalSourceKeyRecipeStream.emittedStream
      (terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    terminalTagsComputableInPolyTime
    TerminalSourceKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def crossingTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingSourceKeyRecipeStream.emittedStream
      (crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    crossingTagsComputableInPolyTime
    CrossingSourceKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      tokens :=
  TM2ListAppend.computableInPolyTime
    terminalTokensComputableInPolyTime crossingTokensComputableInPolyTime

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing

end
