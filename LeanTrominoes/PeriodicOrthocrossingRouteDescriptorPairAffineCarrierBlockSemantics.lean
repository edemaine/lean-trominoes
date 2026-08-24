/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierShapeSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics

/-! # Pair-block semantics of the affine carrier candidate scan -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- A flat map with one potentially nonempty value reduces to its unique
selected branch. -/
private theorem carrierFlatMap_eq_of_unique
    {Index Output : Type}
    (indices : List Index) (function : Index → List Output)
    (selected : Index)
    (nodup : indices.Nodup)
    (selectedMember : selected ∈ indices)
    (othersEmpty :
      ∀ index ∈ indices, index ≠ selected → function index = []) :
    indices.flatMap function = function selected := by
  induction indices with
  | nil => simp at selectedMember
  | cons index indices induction =>
      rw [List.nodup_cons] at nodup
      rcases List.mem_cons.mp selectedMember with selectedHead | selectedTail
      · subst index
        rw [List.flatMap_cons]
        have tailEmpty : indices.flatMap function = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro other otherMember
          exact othersEmpty other (by simp [otherMember]) fun otherEq =>
            nodup.1 (otherEq ▸ otherMember)
        rw [tailEmpty, List.append_nil]
      · have headNe : index ≠ selected := by
          intro headEq
          exact nodup.1 (headEq ▸ selectedTail)
        rw [List.flatMap_cons,
          othersEmpty index (by simp) headNe,
          List.nil_append]
        exact induction nodup.2 selectedTail fun other otherMember otherNe =>
          othersEmpty other (by simp [otherMember]) otherNe

/-- A route shape whose guard fails contributes no carrier candidates. -/
theorem RouteShape.carrierSegmentSelection_eq_nil_of_not_matches
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        shape.carrierSegmentPredicates
        shape.carrierSegmentBitBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.carrierSegmentPredicates
    RouteShape.carrierSegmentBitBlocks
  rw [List.map_flatMap, carrierSelectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro segment _segmentMember
    have guardFalse : (shape.guard .first).evalPair pair = false := by
      rw [shape.evalPair_guard]
      simp [notMatches, descriptorAt]
    simp [Segment.carrierAxisPredicates, carrierAxisNeighborBlocks,
      Predicate.evalTokens_descriptorPairTokens, evalPair_all,
      guardFalse, selectTruthBlocks]
  · intro segment _segmentMember
    simp [Segment.carrierAxisPredicates, carrierAxisNeighborBlocks]

/-- The complete fixed shape scan selects its unique matching route shape
and returns the neighboring axis bits of its evaluated segments. -/
theorem affineCarrierSegmentBitBlock_eq_of_matches
    (selectedShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : selectedShape.Matches pair.1)
    (axisAligned :
      ∀ segment ∈ selectedShape.segments .first,
        (segment.evalPair pair).IsAxisAligned) :
    affineCarrierSegmentBitBlock (descriptorPairTokens pair) =
      (selectedShape.segments .first).flatMap fun segment =>
        neighborTranslations.map fun _ =>
          (decide (segment.evalPair pair).IsHorizontal, false) := by
  unfold affineCarrierSegmentBitBlock carrierSegmentPredicates
    carrierSegmentBitBlocks
  rw [predicateListBlocks_eq, List.map_flatMap,
    carrierSelectTruthBlocks_flatMap]
  · rw [carrierFlatMap_eq_of_unique
      allRouteShapes
      (fun shape =>
        selectTruthBlocks shape.carrierSegmentBitBlocks
          (shape.carrierSegmentPredicates.map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair)))
      selectedShape allRouteShapes_nodup
      (mem_allRouteShapes selectedShape)]
    · rw [← predicateListBlocks_eq]
      exact selectedShape.carrierSegmentSelection_eq pair sameEdge
        shapeMatches axisAligned
    · intro shape _shapeMember shapeNe
      rw [← predicateListBlocks_eq]
      apply shape.carrierSegmentSelection_eq_nil_of_not_matches
      intro otherMatches
      exact shapeNe (RouteShape.eq_of_matches otherMatches shapeMatches)
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.carrierSegmentBitBlocks,
      Segment.carrierAxisPredicates, carrierAxisNeighborBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
