/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for common-shift canonical-left source keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyStream

open Computability Turing

/-- Map the common-shift inner emitter independently over a complete
descriptor-slot pair stream. -/
def emittedStream
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    CanonicalCrossingShiftLeftSourceKeyEmitter.emittedTokens tokens

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    CanonicalCrossingShiftLeftSourceKeyEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

/-- Prepare the complete tagged descriptor-slot square directly from an
encoded route-descriptor word list. -/
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

end CanonicalCrossingShiftLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
