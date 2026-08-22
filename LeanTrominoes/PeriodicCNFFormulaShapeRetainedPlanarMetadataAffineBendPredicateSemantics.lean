/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineBendPortPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegmentSemantics

/-! # Local semantics of affine retained-bend predicates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The one-field diagonal predicate compares the two stored edge indices. -/
theorem sameEdgeIndexPredicate_evalPair
    (pair : RouteDescriptor × RouteDescriptor) :
    sameEdgeIndexPredicate.evalPair pair =
      decide (pair.1.edgeIndex = pair.2.edgeIndex) := by
  rcases pair with ⟨first, second⟩
  rcases first with
    ⟨firstVertexCount, firstEdgeCount, firstEdgeIndex,
      firstSourceVertexIndex, firstTargetVertexIndex,
      firstSourcePortRank, firstTargetPortRank, firstOffset⟩
  rcases second with
    ⟨secondVertexCount, secondEdgeCount, secondEdgeIndex,
      secondSourceVertexIndex, secondTargetVertexIndex,
      secondSourcePortRank, secondTargetPortRank, secondOffset⟩
  simp [sameEdgeIndexPredicate, Predicate.evalPair, Predicate.eval,
    Atom.eval, Relation.eval, Expression.eval,
    Term.eval, term,
    pairFieldValue, descriptorFieldValue,
    RouteDescriptor.unaryFields, signedUnaryFields, field, equal, compare]

/-- On the edge-index diagonal and under the selected route-shape guard, one
combined predicate recognizes exactly its evaluated bend's port pair. -/
theorem BendTemplate.descriptorPredicate_evalPair
    (shape : RouteShape) (template : BendTemplate)
    (ports : CornerPort × CornerPort)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (incomingGenuine :
      (AxisDirection.between
        (template.incomingStart.evalPair pair)
        (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      (AxisDirection.between
        (template.bend.evalPair pair)
        (template.outgoingFinish.evalPair pair)).IsGenuine) :
    (template.descriptorPredicate shape ports).evalPair pair =
      decide
        ((template.evalPair .first pair).incomingPort = ports.1 ∧
          (template.evalPair .first pair).outgoingPort = ports.2) := by
  have shapeMatches' :
      shape.Matches (descriptorAt pair .first) := by
    simpa [descriptorAt] using shapeMatches
  unfold BendTemplate.descriptorPredicate
  simp only [evalPair_all, List.all_cons, List.all_nil, Bool.and_true]
  rw [sameEdgeIndexPredicate_evalPair, shape.evalPair_guard,
    template.portPredicate_evalPair ports.1 ports.2 .first pair
      incomingGenuine outgoingGenuine]
  simp [sameEdge, shapeMatches']

/-- Selecting the sixteen aligned port blocks keeps exactly the canonical
block named by one evaluated genuine bend. -/
theorem BendTemplate.descriptorPredicates_selectedBlock
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (incomingGenuine :
      (AxisDirection.between
        (template.incomingStart.evalPair pair)
        (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      (AxisDirection.between
        (template.bend.evalPair pair)
        (template.outgoingFinish.evalPair pair)).IsGenuine) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        bendTemplateDescriptorBlocks
        (descriptorPairTokens pair) =
      canonicalBendDescriptorBlock
        (template.evalPair .first pair).incomingPort
        (template.evalPair .first pair).outgoingPort false := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates bendTemplateDescriptorBlocks
  rw [List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun ports =>
          canonicalBendDescriptorBlock ports.1 ports.2 false)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = _
  simp_rw [BendTemplate.descriptorPredicate_evalPair shape template _ pair
    sameEdge shapeMatches incomingGenuine outgoingGenuine]
  generalize incomingEq :
      (template.evalPair .first pair).incomingPort = incoming
  generalize outgoingEq :
      (template.evalPair .first pair).outgoingPort = outgoing
  cases incoming <;> cases outgoing <;>
    simp [allCornerPortPairs, allCornerPorts, selectTruthBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
