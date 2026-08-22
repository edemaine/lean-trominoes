/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebra
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSemantics

/-! # Exact semantics of affine expression algebra and points -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

@[simp] theorem Expression.eval_add
    (valuation : Side → Fin 11 → Nat) (first second : Expression) :
    (first.add second).eval valuation =
      first.eval valuation + second.eval valuation := by
  simp [Expression.add, Expression.eval, List.sum_append]
  ring

@[simp] theorem Expression.eval_scale
    (valuation : Side → Fin 11 → Nat) (coefficient : Int)
    (expression : Expression) :
    (expression.scale coefficient).eval valuation =
      coefficient * expression.eval valuation := by
  rcases expression with ⟨constant, terms⟩
  have scaledTerms :
      (List.map (Term.eval valuation)
          (terms.map fun expressionTerm =>
            { expressionTerm with
              coefficient := coefficient * expressionTerm.coefficient })).sum =
        coefficient * (terms.map (Term.eval valuation)).sum := by
    induction terms with
    | nil => simp
    | cons expressionTerm terms induction =>
        simp only [List.map_cons, List.sum_cons]
        rw [induction]
        simp [Term.eval]
        ring
  simp only [Expression.scale, Expression.eval]
  rw [scaledTerms]
  ring

@[simp] theorem Expression.eval_negate
    (valuation : Side → Fin 11 → Nat) (expression : Expression) :
    expression.negate.eval valuation = -expression.eval valuation := by
  simp [Expression.negate]

@[simp] theorem Expression.eval_subtract
    (valuation : Side → Fin 11 → Nat) (first second : Expression) :
    (first.subtract second).eval valuation =
      first.eval valuation - second.eval valuation := by
  simp [Expression.subtract, sub_eq_add_neg]

@[simp] theorem Expression.eval_addConstant
    (valuation : Side → Fin 11 → Nat) (expression : Expression) (value : Int) :
    (expression.addConstant value).eval valuation =
      expression.eval valuation + value := by
  simp [Expression.addConstant, Expression.eval]
  ring

/-- Affine point evaluation is preserved exactly by canonical pair tagging. -/
theorem Point.evalTokens_descriptorPairTokens
    (affinePoint : Point) (pair : RouteDescriptor × RouteDescriptor) :
    affinePoint.evalTokens (descriptorPairTokens pair) =
      affinePoint.evalPair pair := by
  apply Prod.ext
  · exact Expression.evalTokens_descriptorPairTokens
      affinePoint.horizontal pair
  · exact Expression.evalTokens_descriptorPairTokens
      affinePoint.vertical pair

/-- The affine source-center expression is `vertexX` exactly. -/
theorem evalPair_sourceCenterX
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (sourceCenterX side).evalPair pair =
      vertexX (descriptorAt pair side).sourceVertexIndex := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [sourceCenterX, Expression.evalPair, Expression.eval, Term.eval,
      term, pairFieldValue, descriptorFieldValue,
      RouteDescriptor.unaryFields, signedUnaryFields, descriptorAt, vertexX] <;>
    ring

/-- The affine target-center expression is `vertexX` exactly. -/
theorem evalPair_targetCenterX
    (pair : RouteDescriptor × RouteDescriptor) (side : Side) :
    (targetCenterX side).evalPair pair =
      vertexX (descriptorAt pair side).targetVertexIndex := by
  rcases pair with ⟨first, second⟩
  cases side <;>
    rcases first with ⟨vertexCount₁, edgeCount₁, edgeIndex₁,
      sourceVertexIndex₁, targetVertexIndex₁, sourcePortRank₁,
      targetPortRank₁, offset₁⟩ <;>
    rcases second with ⟨vertexCount₂, edgeCount₂, edgeIndex₂,
      sourceVertexIndex₂, targetVertexIndex₂, sourcePortRank₂,
      targetPortRank₂, offset₂⟩ <;>
    simp [targetCenterX, Expression.evalPair, Expression.eval, Term.eval,
      term, pairFieldValue, descriptorFieldValue,
      RouteDescriptor.unaryFields, signedUnaryFields, descriptorAt, vertexX] <;>
    ring

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
