/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnaryData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagAlphabetData

/-! # Lightweight semantic field tags for route-descriptor pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags

def advanceFields : Fin 11 → Nat → Fin 11
  | field, 0 => field
  | field, count + 1 => advanceFields (nextField field) count

/-- Tagged units for a sequence of unary fields beginning at the supplied
field position. -/
def taggedFields : Side → Fin 11 → List Nat → List Token
  | _, _, [] => []
  | side, field, number :: numbers =>
      List.replicate number (.unit side field) ++
        taggedFields side (nextField field) numbers

/-- Tagged units of one canonical eleven-field descriptor. -/
def descriptorUnits (side : Side) (descriptor : RouteDescriptor) :
    List Token :=
  taggedFields side 0 descriptor.unaryFields

/-- Canonical tagged output block for one ordered descriptor pair. -/
def descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) : List Token :=
  .pairStart ::
    (descriptorUnits .first pair.1 ++
      descriptorUnits .second pair.2 ++ [.pairEnd])

/-- Canonical tagged output for a descriptor-pair list. -/
def encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) : List Token :=
  pairs.flatMap descriptorPairTokens

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags
