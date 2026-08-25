/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.TM2NativeListAppendClosure
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Complete doubled source-key component stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- The crossing-only half of the doubled component stream is available as
a reusable compiler before the terminal/crossing append. -/
noncomputable def crossingTokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      crossingTokens := by
  let crossingTagsCompiler :
      TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
        crossingTags := by
    change TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
        (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input))
    exact TM2CompositionMachine.computableInPolyTime
      DelimitedBinaryWordOccurrenceSlotTags.expandedPairsComputableInPolyTime
      RouteDescriptorOccurrenceSlotPairFieldTags.inputTokensComputableInPolyTime
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossingSourceKeyRecipeStream.emittedStream
      (crossingTags input))
  exact TM2CompositionMachine.computableInPolyTime
    crossingTagsCompiler
    CrossingSourceKeyRecipeStream.emittedStreamComputableInPolyTime

noncomputable def descriptorTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors =>
        tokens (RouteDescriptorBinaryWords.words descriptors)) := by
  let tokensCompiler :
      TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
        tokens := by
    let terminalTagsCompiler :
        TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
          terminalTags := by
      change TM2ComputableInPolyTime
        DelimitedBinaryWords.finEncoding.encode id
        (fun input => RouteDescriptorPairFieldTags.inputTokens
          (DelimitedBinaryWordPairProductMachine.pairs input))
      exact TM2CompositionMachine.computableInPolyTime
        DelimitedBinaryWordPairProductMachine.computableInPolyTime
        RouteDescriptorPairFieldTags.inputTokensComputableInPolyTime
    let crossingTagsCompiler :
        TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
          crossingTags := by
      change TM2ComputableInPolyTime
        DelimitedBinaryWords.finEncoding.encode id
        (fun input => RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
          (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input))
      exact TM2CompositionMachine.computableInPolyTime
        DelimitedBinaryWordOccurrenceSlotTags.expandedPairsComputableInPolyTime
        RouteDescriptorOccurrenceSlotPairFieldTags.inputTokensComputableInPolyTime
    let terminalCompiler :
        TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
          terminalTokens := by
      change TM2ComputableInPolyTime
        DelimitedBinaryWords.finEncoding.encode id
        (fun input => TerminalSourceKeyRecipeStream.emittedStream
          (terminalTags input))
      exact TM2CompositionMachine.computableInPolyTime
        terminalTagsCompiler
        TerminalSourceKeyRecipeStream.emittedStreamComputableInPolyTime
    let crossingCompiler :
        TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
          crossingTokens := by
      change TM2ComputableInPolyTime
        DelimitedBinaryWords.finEncoding.encode id
        (fun input => CrossingSourceKeyRecipeStream.emittedStream
          (crossingTags input))
      exact TM2CompositionMachine.computableInPolyTime
        crossingTagsCompiler
        CrossingSourceKeyRecipeStream.emittedStreamComputableInPolyTime
    exact TM2ListAppend.computableInPolyTime
      terminalCompiler crossingCompiler
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words tokensCompiler
    (fun _ => rfl) (fun _ => rfl)

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing

end
