/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeStreamCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Complete terminal-prefix/crossing-suffix carrier-key recipe stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

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
  TerminalCarrierKeyRecipeStream.emittedStream (terminalTags input)

def crossingTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CrossingCarrierKeyRecipeStream.emittedStream (crossingTags input)

/-- Complete padded candidate-word stream, with the terminal prefix before
the slot-major crossing suffix. -/
def emittedTokens (input : DelimitedBinaryWords.Input) :
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
    (fun input => TerminalCarrierKeyRecipeStream.emittedStream
      (terminalTags input))
  exact TM2CompositionMachine.computableInPolyTime
    terminalTagsComputableInPolyTime
    TerminalCarrierKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def crossingTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingTokens := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingCarrierKeyRecipeStream.emittedStream
      (crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    crossingTagsComputableInPolyTime
    CrossingCarrierKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      emittedTokens := by
  exact TM2ListAppend.computableInPolyTime
    terminalTokensComputableInPolyTime crossingTokensComputableInPolyTime

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
