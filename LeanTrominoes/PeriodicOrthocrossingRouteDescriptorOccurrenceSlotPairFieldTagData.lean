/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagAlphabetData

/-! # Lightweight twelve-field occurrence-slot pair tags -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

def advanceFields : Fin 12 → Nat → Fin 12
  | field, 0 => field
  | field, count + 1 => advanceFields (nextField field) count

/-- Tagged units for a sequence of unary fields beginning at the supplied
field position. -/
def taggedFields : Side → Fin 12 → List Nat → List Token
  | _, _, [] => []
  | side, field, number :: numbers =>
      List.replicate number (.unit side field) ++
        taggedFields side (nextField field) numbers

/-- Eleven descriptor fields followed by the occurrence-slot field. -/
def descriptorSlotFields
    (tagged : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List Nat :=
  tagged.1.unaryFields ++ [tagged.2.val]

/-- Canonical tagged units for one descriptor occurrence slot. -/
def descriptorSlotUnits
    (side : Side)
    (tagged : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List Token :=
  taggedFields side 0 (descriptorSlotFields tagged)

/-- Canonical tagged output for one ordered descriptor-slot pair. -/
def descriptorSlotPairTokens
    (pair :
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
        RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List Token :=
  .pairStart ::
    (descriptorSlotUnits .first pair.1 ++
      descriptorSlotUnits .second pair.2 ++ [.pairEnd])

/-- Canonical tagged output for a descriptor-slot pair list. -/
def encodeDescriptorSlotPairs
    (pairs : List
      (RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
        RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor)) :
    List Token :=
  pairs.flatMap descriptorSlotPairTokens

/-- Forget slot-field units, converting the remaining stream to the existing
eleven-field descriptor-pair alphabet. -/
def descriptorProjection : Token → List RouteDescriptorPairFieldTags.Token
  | .pairStart => [.pairStart]
  | .pairEnd => [.pairEnd]
  | .unit side field =>
      if within : field.val < 11 then
        [.unit side ⟨field.val, within⟩]
      else
        []

/-- Project a complete twelve-field stream to its descriptor-only tags. -/
def descriptorTokens (source : List Token) :
    List RouteDescriptorPairFieldTags.Token :=
  source.flatMap descriptorProjection

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
