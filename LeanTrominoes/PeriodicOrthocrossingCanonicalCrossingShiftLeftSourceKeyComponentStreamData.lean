/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData

/-! # Component fields of shifted canonical crossing source keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyComponentStream

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords

/-- The complete padded carrier-node candidate stream underlying the compact
source-pair candidates. -/
def carrierNodeCandidates
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (Candidate CarrierNode) :=
  pairs.flatMap
    RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftCarrierNodeCandidates

/-- The adjacent guarded carrier-key components of every shifted candidate. -/
def componentPairs
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (List Bool × List Bool) :=
  CarrierNodeSourceKeyCandidateWords.componentPairs
    (carrierNodeCandidates pairs)

/-- Select one component of a carrier node's compact source-key pair. -/
def sourceKey (side : DelimitedBinaryWordPairSelector.Side)
    (node : CarrierNode) : CarrierKeyWords.CarrierKey :=
  match side with
  | .first => (CarrierNodeSourceKeys.pair node).1
  | .second => (CarrierNodeSourceKeys.pair node).2

/-- Select one optional carrier key from every padded source pair. -/
def selectedKeys (side : DelimitedBinaryWordPairSelector.Side)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values (carrierNodeCandidates pairs)).map
    (Option.map (sourceKey side))

/-- One aligned unary component field followed by the lookup sentinel. -/
def fieldValuesWithSentinel
    (side : DelimitedBinaryWordPairSelector.Side)
    (field : CarrierKeyFieldProjector.Field)
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) : List Nat :=
  (selectedKeys side pairs).map (CarrierKeyFieldProjector.value field) ++ [0]

end CanonicalCrossingShiftLeftSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
