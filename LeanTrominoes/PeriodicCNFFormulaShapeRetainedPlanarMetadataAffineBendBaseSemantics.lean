/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendShapeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics

/-! # Base-route semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- A flat-map with one potentially nonempty value reduces to that uniquely
indexed value. -/
theorem flatMap_eq_of_unique
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

/-- If a route-shape guard fails, every bend predicate carrying that guard
selects the empty block. -/
theorem BendTemplate.descriptorPredicates_eq_nil_of_not_matches
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateDescriptorBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates bendTemplateDescriptorBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports =>
          canonicalBendDescriptorBlock ports.1 ports.2 false)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = []
  have guardFalse :
      (shape.guard .first).evalPair pair = false := by
    rw [shape.evalPair_guard]
    simp [notMatches, descriptorAt]
  have predicateFalse :
      ∀ ports,
        (template.descriptorPredicate shape ports).evalPair pair = false := by
    intro ports
    simp [BendTemplate.descriptorPredicate, evalPair_all, guardFalse]
  simp [allCornerPortPairs, allCornerPorts,
    selectTruthBlocks, predicateFalse]

/-- A nonmatching route shape contributes no descriptor blocks. -/
theorem RouteShape.bendDescriptorSelection_eq_nil_of_not_matches
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.1) :
    predicateListBlocks
        shape.bendDescriptorPredicates
        shape.bendDescriptorBlocks
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.bendDescriptorPredicates
    RouteShape.bendDescriptorBlocks
  rw [List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro template templateMember
    rw [← predicateListBlocks_eq]
    exact template.descriptorPredicates_eq_nil_of_not_matches
      shape pair notMatches
  · intro template _templateMember
    simp [BendTemplate.descriptorPredicates,
      bendTemplateDescriptorBlocks]

/-- The complete fixed shape scan selects the unique matching route shape
and returns precisely its evaluated base-bend descriptor sequence. -/
theorem affineBaseBendDescriptorBlock_eq_of_matches
    (selectedShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : selectedShape.Matches pair.1)
    (incomingGenuine :
      ∀ template ∈ selectedShape.baseBendTemplates,
        (AxisDirection.between
          (template.incomingStart.evalPair pair)
          (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      ∀ template ∈ selectedShape.baseBendTemplates,
        (AxisDirection.between
          (template.bend.evalPair pair)
          (template.outgoingFinish.evalPair pair)).IsGenuine) :
    affineBaseBendDescriptorBlock (descriptorPairTokens pair) =
      selectedShape.baseBendTemplates.flatMap fun template =>
        canonicalBendDescriptorBlock
          (template.evalPair .first pair).incomingPort
          (template.evalPair .first pair).outgoingPort false := by
  unfold affineBaseBendDescriptorBlock bendDescriptorPredicates
    bendDescriptorBlocks
  rw [predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · rw [flatMap_eq_of_unique
      allRouteShapes
      (fun shape =>
        selectTruthBlocks shape.bendDescriptorBlocks
          (shape.bendDescriptorPredicates.map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair)))
      selectedShape allRouteShapes_nodup
      (mem_allRouteShapes selectedShape)]
    · rw [← predicateListBlocks_eq]
      exact selectedShape.bendDescriptorSelection_eq pair sameEdge
        shapeMatches incomingGenuine outgoingGenuine
    · intro shape shapeMember shapeNe
      rw [← predicateListBlocks_eq]
      apply shape.bendDescriptorSelection_eq_nil_of_not_matches
      intro otherMatches
      exact shapeNe
        (RouteShape.eq_of_matches otherMatches shapeMatches)
  · intro shape _shapeMember
    simp [RouteShape.bendDescriptorPredicates,
      RouteShape.bendDescriptorBlocks,
      BendTemplate.descriptorPredicates,
      bendTemplateDescriptorBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
