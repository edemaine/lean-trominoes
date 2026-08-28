/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyComponentStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorData

/-! # All fields of shifted canonical crossing source-key pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyAllFieldStream

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

/-- Both optional carrier-key components of every padded candidate, in
candidate-major and first-then-second order. -/
def componentKeys
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values
    (CanonicalCrossingShiftLeftSourceKeyComponentStream.carrierNodeCandidates
      pairs)).flatMap fun node =>
        [node.map
            (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
              .first),
          node.map
            (CanonicalCrossingShiftLeftSourceKeyComponentStream.sourceKey
              .second)]

/-- Twelve unary fields per padded source pair, followed by one twelve-zero
rejection sentinel block. -/
def fieldValuesWithSentinel
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) : List Nat :=
  CarrierKeyAllFieldProjector.valuesWithSentinel (componentKeys pairs)

end CanonicalCrossingShiftLeftSourceKeyAllFieldStream
end LeanTrominoes.PeriodicOrthocrossing
