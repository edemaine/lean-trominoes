/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
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

end CanonicalCrossingShiftLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
