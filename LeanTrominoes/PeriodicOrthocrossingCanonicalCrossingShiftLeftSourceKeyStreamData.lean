/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateData

/-! # Guarded common-shift canonical-left source-key streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyStream

open RouteDescriptorOccurrenceSlotBinaryWords

/-- Concatenate the fixed guarded common-shift candidates emitted for every
descriptor-slot pair. -/
def guardedWords (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (List Bool) :=
  pairs.flatMap fun pair =>
    (RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyCandidates
      pair).map
        (PaddedSupportedCandidateWords.guardedWord
          CarrierNodeSourceKeys.word)

/-- The complete option-valued source-pair candidate stream. -/
def candidates (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (PaddedSupportedLastRepresentativeEqualityRows.Candidate
      CarrierNodeSourceKeys.SourceKeyPair) :=
  pairs.flatMap
    RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyCandidates

end CanonicalCrossingShiftLeftSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing
