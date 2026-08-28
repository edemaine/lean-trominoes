/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for canonical-left crossing source keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingLeftSourceKeyStream

open Computability Turing

/-- Map the canonical-left inner emitter independently over a complete
descriptor-slot pair stream. -/
def emittedStream
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    CanonicalCrossingLeftSourceKeyEmitter.emittedTokens tokens

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    CanonicalCrossingLeftSourceKeyEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

end CanonicalCrossingLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
