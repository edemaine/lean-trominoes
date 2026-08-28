/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.DelimitedBinaryWordPairSelectorCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyComponentStreamData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for shifted canonical crossing source-key component fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyComponentStream

open Computability Turing

/-- Map the unmerged two-component emitter over every descriptor-slot pair. -/
def emittedStream
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    CanonicalCrossingShiftLeftSourceKeyRecipeEmitter.emittedTokens tokens

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    CanonicalCrossingShiftLeftSourceKeyRecipeEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

/-- Prepare the full tagged descriptor-slot square and emit every guarded
component pair. -/
def emittedDescriptorStream (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  emittedStream
    (RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
      (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input))

noncomputable def emittedDescriptorStreamComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id emittedDescriptorStream := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    (fun input => emittedStream
      (RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
        (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input)))
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      DelimitedBinaryWordOccurrenceSlotTags.expandedPairsComputableInPolyTime
      RouteDescriptorOccurrenceSlotPairFieldTags.inputTokensComputableInPolyTime)
    emittedStreamComputableInPolyTime

/-- Select one component of every adjacent guarded source-key pair. -/
def selectedStream (side : DelimitedBinaryWordPairSelector.Side)
    (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordPairSelector.tokens side (emittedDescriptorStream input)

noncomputable def selectedStreamComputableInPolyTime
    (side : DelimitedBinaryWordPairSelector.Side) :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id (selectedStream side) := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    (fun input => DelimitedBinaryWordPairSelector.tokens side
      (emittedDescriptorStream input))
  exact TM2CompositionMachine.computableInPolyTime
    emittedDescriptorStreamComputableInPolyTime
    (DelimitedBinaryWordPairSelector.tokensComputableInPolyTime side)

/-- Project one of the six unary fields from the selected component stream. -/
def fieldStream (side : DelimitedBinaryWordPairSelector.Side)
    (field : CarrierKeyFieldProjector.Field)
    (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  CarrierKeyFieldProjector.output field (selectedStream side input)

noncomputable def fieldStreamComputableInPolyTime
    (side : DelimitedBinaryWordPairSelector.Side)
    (field : CarrierKeyFieldProjector.Field) :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id (fieldStream side field) := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    (fun input => CarrierKeyFieldProjector.output field
      (selectedStream side input))
  exact TM2CompositionMachine.computableInPolyTime
    (selectedStreamComputableInPolyTime side)
    (CarrierKeyFieldProjector.computableInPolyTime field)

end CanonicalCrossingShiftLeftSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing

end
