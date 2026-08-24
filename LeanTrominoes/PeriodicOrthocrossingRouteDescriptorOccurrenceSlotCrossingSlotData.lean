/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingPredicateListData

/-! # Lightweight slot-guarded affine crossing data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- One affine occurrence-pair predicate together with the exact fixed slots
occupied by its two occurrence templates. -/
structure Slot where
  descriptorPredicate : Predicate
  occurrences : Occurrence × Occurrence
  firstSlot : Nat
  secondSlot : Nat
  deriving DecidableEq

/-- Numeric value of the twelfth unary field on one side of a tagged pair. -/
def slotValue
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token)
    (side : RouteDescriptorPairFieldTags.Side) : Nat :=
  tokens.count (.unit side (11 : Fin 12))

/-- A crossing slot accepts exactly when its descriptor predicate holds and
the two runtime slot fields select its occurrence templates. -/
def Slot.evalTokens
    (slot : Slot)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) : Bool :=
  slot.descriptorPredicate.evalTokens (descriptorTokens tokens) &&
    decide (slotValue tokens .first = slot.firstSlot) &&
    decide (slotValue tokens .second = slot.secondSlot)

/-- Crossing slots for one fixed route-shape pair, in the same row-major
occurrence order as `routeShapePairCrossingPredicates`. -/
def routeShapePairCrossingSlots
    (shapes : RouteShape × RouteShape) : List Slot :=
  ((shapes.1.occurrences .first).zipIdx ×ˢ
      (shapes.2.occurrences .second).zipIdx).map fun pair =>
    { descriptorPredicate :=
        guardedCrossingPredicate shapes (pair.1.1, pair.2.1)
      occurrences := (pair.1.1, pair.2.1)
      firstSlot := pair.1.2
      secondSlot := pair.2.2 }

/-- Complete fixed slot-guarded scan, aligned with
`affineCrossingPredicates`. -/
def crossingSlots : List Slot :=
  (allRouteShapes ×ˢ allRouteShapes).flatMap
    routeShapePairCrossingSlots

/-- One activation bit per fixed slot-guarded affine crossing. -/
def crossingActivations
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List Bool :=
  crossingSlots.map fun slot => slot.evalTokens tokens

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
