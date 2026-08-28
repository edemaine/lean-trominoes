/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyComponentStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.TM2NativeListAppendClosure
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Complete normalized carrier source-key component compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyComponentStream

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

noncomputable def descriptorTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      id
      (fun descriptors =>
        tokens (RouteDescriptorBinaryWords.words descriptors)) := by
  let terminalTagsCompiler :
      TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
        CarrierSourceKeyComponentStream.terminalTags := by
    change TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => RouteDescriptorPairFieldTags.inputTokens
        (DelimitedBinaryWordPairProductMachine.pairs input))
    exact TM2CompositionMachine.computableInPolyTime
      DelimitedBinaryWordPairProductMachine.computableInPolyTime
      RouteDescriptorPairFieldTags.inputTokensComputableInPolyTime
  let crossingTagsCompiler :
      TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
        CarrierSourceKeyComponentStream.crossingTags := by
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
      (fun input =>
        CarrierNormalizedSourceKeyRecipeStream.terminalEmittedStream
          (CarrierSourceKeyComponentStream.terminalTags input))
    exact TM2CompositionMachine.computableInPolyTime
      terminalTagsCompiler
      CarrierNormalizedSourceKeyRecipeStream.terminalEmittedStreamComputableInPolyTime
  let crossingCompiler :
      TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
        crossingTokens := by
    change TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input =>
        CarrierNormalizedSourceKeyRecipeStream.crossingEmittedStream
          (CarrierSourceKeyComponentStream.crossingTags input))
    exact TM2CompositionMachine.computableInPolyTime
      crossingTagsCompiler
      CarrierNormalizedSourceKeyRecipeStream.crossingEmittedStreamComputableInPolyTime
  let tokensCompiler :
      TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
        tokens :=
    TM2ListAppend.computableInPolyTime terminalCompiler crossingCompiler
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words tokensCompiler
    (fun _ => rfl) (fun _ => rfl)

end CarrierNormalizedSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing

end
