/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairAffineData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSemantics

/-! # Semantic field projections for routed-variable pair predicates -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open PeriodicOrthocrossing.RouteDescriptorPairAffine
open PeriodicOrthocrossing.RouteDescriptorPairFieldTags

@[simp] theorem routedVariablePairEdgeIndex_evalPair
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (routedVariablePairEdgeIndex side).evalPair pair =
      ((descriptorAt pair side).edgeIndex : Int) := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with
      ⟨vertexCount₁, edgeCount₁, edgeIndex₁, sourceVertexIndex₁,
        targetVertexIndex₁, sourcePortRank₁, targetPortRank₁, offset₁⟩ <;>
    rcases second with
      ⟨vertexCount₂, edgeCount₂, edgeIndex₂, sourceVertexIndex₂,
        targetVertexIndex₂, sourcePortRank₂, targetPortRank₂, offset₂⟩ <;>
    simp [routedVariablePairEdgeIndex, field, Expression.evalPair,
      Expression.eval, Term.eval, term, pairFieldValue,
      descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt]

@[simp] theorem routedVariablePairTargetVertexIndex_evalPair
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (routedVariablePairTargetVertexIndex side).evalPair pair =
      ((descriptorAt pair side).targetVertexIndex : Int) := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with
      ⟨vertexCount₁, edgeCount₁, edgeIndex₁, sourceVertexIndex₁,
        targetVertexIndex₁, sourcePortRank₁, targetPortRank₁, offset₁⟩ <;>
    rcases second with
      ⟨vertexCount₂, edgeCount₂, edgeIndex₂, sourceVertexIndex₂,
        targetVertexIndex₂, sourcePortRank₂, targetPortRank₂, offset₂⟩ <;>
    simp [routedVariablePairTargetVertexIndex, field,
      Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt]

@[simp] theorem routedVariablePairTargetPortRank_evalPair
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (routedVariablePairTargetPortRank side).evalPair pair =
      ((descriptorAt pair side).targetPortRank : Int) := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with
      ⟨vertexCount₁, edgeCount₁, edgeIndex₁, sourceVertexIndex₁,
        targetVertexIndex₁, sourcePortRank₁, targetPortRank₁, offset₁⟩ <;>
    rcases second with
      ⟨vertexCount₂, edgeCount₂, edgeIndex₂, sourceVertexIndex₂,
        targetVertexIndex₂, sourcePortRank₂, targetPortRank₂, offset₂⟩ <;>
    simp [routedVariablePairTargetPortRank, field, Expression.evalPair,
      Expression.eval, Term.eval, term, pairFieldValue,
      descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
