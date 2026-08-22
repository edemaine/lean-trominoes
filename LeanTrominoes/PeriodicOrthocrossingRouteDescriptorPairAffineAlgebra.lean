/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressions

/-! # Algebra and points for affine route-descriptor pair expressions -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Sum two flattened affine expressions. -/
def Expression.add (first second : Expression) : Expression :=
  ⟨first.constant + second.constant, first.terms ++ second.terms⟩

/-- Multiply a flattened affine expression by a fixed signed coefficient. -/
def Expression.scale (coefficient : Int) (expression : Expression) : Expression :=
  ⟨coefficient * expression.constant,
    expression.terms.map fun expressionTerm =>
      { expressionTerm with
        coefficient := coefficient * expressionTerm.coefficient }⟩

/-- Negate a flattened affine expression. -/
def Expression.negate (expression : Expression) : Expression :=
  expression.scale (-1)

/-- Subtract two flattened affine expressions. -/
def Expression.subtract (first second : Expression) : Expression :=
  first.add second.negate

/-- Add a fixed signed constant to an affine expression. -/
def Expression.addConstant (expression : Expression) (value : Int) : Expression :=
  ⟨expression.constant + value, expression.terms⟩

/-- A grid point whose two coordinates are fixed affine expressions. -/
structure Point where
  horizontal : Expression
  vertical : Expression
  deriving DecidableEq

/-- Evaluate an affine grid point under a natural-valued field assignment. -/
def Point.eval
    (valuation : Side → Fin 11 → Nat) (point : Point) : Cell :=
  (point.horizontal.eval valuation, point.vertical.eval valuation)

/-- Evaluate an affine point on the semantic fields of a descriptor pair. -/
def Point.evalPair
    (point : Point) (pair : RouteDescriptor × RouteDescriptor) : Cell :=
  point.eval (pairFieldValue pair)

/-- Evaluate an affine point by counting tagged unary units. -/
def Point.evalTokens
    (point : Point) (tokens : List RouteDescriptorPairFieldTags.Token) : Cell :=
  point.eval (tokenFieldValue tokens)

/-- Construct an affine point from its coordinate expressions. -/
def point (horizontal vertical : Expression) : Point :=
  ⟨horizontal, vertical⟩

/-- The source vertex-center column `8 * sourceVertexIndex + 4`. -/
def sourceCenterX (side : Side) : Expression :=
  ⟨4, [term 8 side 3]⟩

/-- The target vertex-center column `8 * targetVertexIndex + 4`. -/
def targetCenterX (side : Side) : Expression :=
  ⟨4, [term 8 side 4]⟩

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
