/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentSelectionSemantics

/-! # Route-shape semantics of the affine carrier candidate scan -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Block selection distributes across an aligned prefix append. -/
private theorem carrierSelectTruthBlocks_append
    {Output : Type}
    (firstBlocks secondBlocks : List (List Output))
    (firstTruths secondTruths : List Bool)
    (lengthEq : firstBlocks.length = firstTruths.length) :
    selectTruthBlocks
        (firstBlocks ++ secondBlocks) (firstTruths ++ secondTruths) =
      selectTruthBlocks firstBlocks firstTruths ++
        selectTruthBlocks secondBlocks secondTruths := by
  induction firstBlocks generalizing firstTruths with
  | nil =>
      have firstTruthsNil : firstTruths = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst firstTruths
      rfl
  | cons block blocks induction =>
      cases firstTruths with
      | nil => simp at lengthEq
      | cons truth truths =>
          have tailLengthEq : blocks.length = truths.length := by
            simpa using lengthEq
          simp only [List.cons_append, selectTruthBlocks]
          rw [induction truths tailLengthEq]
          cases truth <;> simp [List.append_assoc]

/-- Block selection distributes over an aligned fixed flat-map family. -/
private theorem carrierSelectTruthBlocks_flatMap
    {Index Output : Type}
    (indices : List Index)
    (blocks : Index → List (List Output))
    (truths : Index → List Bool)
    (lengthEq :
      ∀ index ∈ indices, (blocks index).length = (truths index).length) :
    selectTruthBlocks
        (indices.flatMap blocks) (indices.flatMap truths) =
      indices.flatMap fun index =>
        selectTruthBlocks (blocks index) (truths index) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons]
      rw [carrierSelectTruthBlocks_append]
      · rw [induction]
        intro tailIndex tailMember
        exact lengthEq tailIndex
          (List.mem_cons_of_mem index tailMember)
      · exact lengthEq index (List.mem_cons_self)

/-- A selected route shape contributes the neighboring axis-bit block of
each evaluated segment in segment-major order. -/
theorem RouteShape.carrierSegmentSelection_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (axisAligned :
      ∀ segment ∈ shape.segments .first,
        (segment.evalPair pair).IsAxisAligned) :
    predicateListBlocks
        shape.carrierSegmentPredicates
        shape.carrierSegmentBitBlocks
        (descriptorPairTokens pair) =
      (shape.segments .first).flatMap fun segment =>
        neighborTranslations.map fun _ =>
          (decide (segment.evalPair pair).IsHorizontal, false) := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.carrierSegmentPredicates
    RouteShape.carrierSegmentBitBlocks
  rw [List.map_flatMap]
  rw [carrierSelectTruthBlocks_flatMap]
  · apply List.flatMap_congr
    intro segment segmentMember
    rw [← predicateListBlocks_eq]
    exact segment.carrierAxisSelection_eq shape pair sameEdge
      shapeMatches (axisAligned segment segmentMember)
  · intro segment _segmentMember
    simp [Segment.carrierAxisPredicates, carrierAxisNeighborBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
