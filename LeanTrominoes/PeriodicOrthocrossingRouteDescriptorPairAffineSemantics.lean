/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressions
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnarySemantics

/-! # Exact semantics of affine route-descriptor pair expressions -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Every affine expression has the same value on a canonical pair block as
on the semantic descriptor pair that generated the block. -/
theorem Expression.evalTokens_descriptorPairTokens
    (expression : Expression)
    (pair : RouteDescriptor × RouteDescriptor) :
    expression.evalTokens (descriptorPairTokens pair) =
      expression.evalPair pair := by
  unfold Expression.evalTokens Expression.evalPair Expression.eval
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro expressionTerm expressionTermMem
  simp only [Term.eval]
  rw [tokenFieldValue_descriptorPairTokens]

/-- The affine period expression is the descriptor's exact grid size. -/
theorem evalPair_gridSize (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) :
    (gridSize side).evalPair pair =
      ((descriptorAt pair side).gridSize : Int) := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [gridSize, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt, RouteDescriptor.gridSize] <;>
    ring

/-- The affine source-column expression is `descriptorPortX` exactly. -/
theorem evalPair_sourcePortX (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) :
    (sourcePortX side).evalPair pair =
      descriptorPortX (descriptorAt pair side).sourceVertexIndex
        (descriptorAt pair side).sourcePortRank := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [sourcePortX, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt, descriptorPortX, vertexX] <;>
    ring

/-- The affine target-column expression is `descriptorPortX` exactly. -/
theorem evalPair_targetPortX (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) :
    (targetPortX side).evalPair pair =
      descriptorPortX (descriptorAt pair side).targetVertexIndex
        (descriptorAt pair side).targetPortRank := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [targetPortX, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt, descriptorPortX, vertexX] <;>
    ring

/-- The affine low-track expression is `edgeTrack` exactly. -/
theorem evalPair_lowTrack (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) :
    (lowTrack side).evalPair pair =
      edgeTrack (descriptorAt pair side).edgeIndex := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [lowTrack, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt, edgeTrack]

/-- The affine high-track expression is one above `edgeTrack`. -/
theorem evalPair_highTrack (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) :
    (highTrack side).evalPair pair =
      edgeTrack (descriptorAt pair side).edgeIndex + 1 := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [highTrack, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt, edgeTrack] <;>
    ring

/-- The affine gate expression is the route's exact vertical gate column. -/
theorem evalPair_gateX (pair : RouteDescriptor × RouteDescriptor)
    (side : Side) :
    (gateX side).evalPair pair =
      8 * (descriptorAt pair side).vertexCount + 4 +
        2 * (descriptorAt pair side).edgeIndex := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [gateX, Expression.evalPair, Expression.eval, Term.eval, term,
      pairFieldValue, descriptorFieldValue, RouteDescriptor.unaryFields,
      signedUnaryFields, descriptorAt] <;>
    ring

/-- The two signed horizontal unary fields recover the exact offset. -/
theorem evalPair_horizontalOffset
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (horizontalOffset side).evalPair pair =
      (descriptorAt pair side).offset.1 := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, ⟨horizontal₁, vertical₁⟩⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, ⟨horizontal₂, vertical₂⟩⟩ <;>
    cases horizontal₁ <;> cases horizontal₂ <;>
    simp [horizontalOffset, Expression.evalPair, Expression.eval, Term.eval,
      term, pairFieldValue, descriptorFieldValue,
      RouteDescriptor.unaryFields, signedUnaryFields, descriptorAt] <;> omega

/-- The two signed vertical unary fields recover the exact offset. -/
theorem evalPair_verticalOffset
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (verticalOffset side).evalPair pair =
      (descriptorAt pair side).offset.2 := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, ⟨horizontal₁, vertical₁⟩⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, ⟨horizontal₂, vertical₂⟩⟩ <;>
    cases vertical₁ <;> cases vertical₂ <;>
    simp [verticalOffset, Expression.evalPair, Expression.eval, Term.eval,
      term, pairFieldValue, descriptorFieldValue,
      RouteDescriptor.unaryFields, signedUnaryFields, descriptorAt] <;> omega

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
