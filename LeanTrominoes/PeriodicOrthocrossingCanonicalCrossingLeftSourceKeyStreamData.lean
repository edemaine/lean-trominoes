/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyCandidateData

/-! # Guarded canonical-left source-key pair streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingLeftSourceKeyStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Concatenate the fixed guarded canonical-left candidates emitted for every
descriptor-slot pair. -/
def guardedWords (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    (RouteDescriptorOccurrenceSlotCrossing.canonicalLeftSourceKeyCandidates
      pair).map
        (PaddedSupportedCandidateWords.guardedWord
          CarrierNodeSourceKeys.word)

end CanonicalCrossingLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing
