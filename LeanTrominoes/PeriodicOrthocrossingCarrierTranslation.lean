/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree

/-!
# Translating retained carrier data

Periodic ownership is useful only if a physical link can be moved to its
zero-shift representative without changing the normalized periodic link.
This file supplies that algebra.  Crossing records, boundaries, terminals,
carrier nodes, equality positions, and equality links all receive a common
lattice translation.  Crossing normalization is invariant, normalization
offsets add the common shift, and `PeriodicEquality.normalizeLink` cancels it.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Translate the occurrence coordinate of a physical carrier key. -/
def periodTranslateCarrierKey
    (key : Nat × Nat × Cell) (shift : Cell) :
    Nat × Nat × Cell :=
  (key.1, key.2.1, Cell.add key.2.2 shift)

/-- Translating a carrier node translates exactly its occurrence key. -/
@[simp]
theorem CarrierNode.carrierKey_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).carrierKey =
      periodTranslateCarrierKey node.carrierKey shift := by
  cases node with
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      simp [CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        periodTranslateCarrierKey,
        CarrierNode.carrierKey,
        SegmentTerminal.carrierKey,
        PeriodicGridDrawing.SegmentOccurrenceKey]
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      rcases crossing with
        ⟨first, firstTranslate, second, secondTranslate, point⟩
      cases side <;>
        simp [CarrierNode.periodTranslate,
          CrossingBoundary.periodTranslate,
          CrossingRecord.periodTranslate,
          periodTranslateCarrierKey,
          CarrierNode.carrierKey,
          CrossingBoundary.carrierKey,
          PeriodicGridDrawing.SegmentOccurrenceKey]

/-- Translating a carrier node preserves its periodic prototype and adds the
common shift to its normalization offset. -/
theorem normalizeCarrierNode_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    normalizeCarrierNode graph
        (node.periodTranslate graph shift) =
      ((normalizeCarrierNode graph node).1,
        Cell.add (normalizeCarrierNode graph node).2 shift) := by
  cases node with
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      simp [CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        normalizeCarrierNode]
  | boundary boundary =>
      change
        (PeriodicCarrierNode.boundary
            ((boundary.periodTranslate graph shift).periodNormalize graph),
          crossingPeriodShift graph
            (boundary.periodTranslate graph shift).crossing) =
        (PeriodicCarrierNode.boundary
            (boundary.periodNormalize graph),
          Cell.add
            (crossingPeriodShift graph boundary.crossing) shift)
      rw [CrossingBoundary.periodNormalize_periodTranslate]
      apply Prod.ext
      · rfl
      · simpa [CrossingBoundary.periodTranslate] using
          crossingPeriodShift_periodTranslate
            graph boundary.crossing shift

/-- A common physical translation cancels out of the normalized periodic
equality link. -/
@[simp]
theorem normalizeLink_carrierLinkPeriodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (carrierLinkPeriodTranslate graph link shift) =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        link := by
  rcases shift with ⟨shiftX, shiftY⟩
  rcases normalizeCarrierNode graph link.first with
    ⟨first, ⟨firstX, firstY⟩⟩
  rcases normalizeCarrierNode graph link.second with
    ⟨second, ⟨secondX, secondY⟩⟩
  simp [PeriodicEquality.normalizeLink,
    carrierLinkPeriodTranslate,
    normalizeCarrierNode_periodTranslate,
    Cell.add, Cell.sub]

end PeriodicOrthocrossing
end LeanTrominoes
