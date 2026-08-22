/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairLengthComparisonMachine
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebra
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicates

/-! # Natural positive and negative totals of signed affine expressions -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open DelimitedBinaryWordPairLengthComparisonMachine

/-- Positive unary contribution of one signed affine term. -/
def Term.positiveCount
    (valuation : Side → Fin 11 → Nat) (expressionTerm : Term) : Nat :=
  expressionTerm.coefficient.toNat *
    valuation expressionTerm.side expressionTerm.field

/-- Negative unary contribution of one signed affine term. -/
def Term.negativeCount
    (valuation : Side → Fin 11 → Nat) (expressionTerm : Term) : Nat :=
  (-expressionTerm.coefficient).toNat *
    valuation expressionTerm.side expressionTerm.field

/-- Total positive unary magnitude of an affine expression. -/
def Expression.positiveCount
    (valuation : Side → Fin 11 → Nat) (expression : Expression) : Nat :=
  expression.constant.toNat +
    (expression.terms.map (Term.positiveCount valuation)).sum

/-- Total negative unary magnitude of an affine expression. -/
def Expression.negativeCount
    (valuation : Side → Fin 11 → Nat) (expression : Expression) : Nat :=
  (-expression.constant).toNat +
    (expression.terms.map (Term.negativeCount valuation)).sum

/-- Positive and negative totals represented physically by tagged unary
descriptor-pair fields. -/
def Expression.tokenCounts
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) : Nat × Nat :=
  (expression.positiveCount (tokenFieldValue tokens),
    expression.negativeCount (tokenFieldValue tokens))

/-- Signed difference of the two sides of an affine comparison. -/
def Atom.difference (atom : Atom) : Expression :=
  atom.first.subtract atom.second

/-- Interpret a length-ordering result according to one affine relation. -/
def Relation.acceptsOrdering : Relation → LengthOrdering → Bool
  | .equal, .equal => true
  | .equal, _ => false
  | .notEqual, .equal => false
  | .notEqual, _ => true
  | .less, .less => true
  | .less, _ => false
  | .lessEqual, .greater => false
  | .lessEqual, _ => true

/-- Evaluate an atom by comparing the positive and negative unary totals of
its signed difference. -/
def Atom.evalFromTokenCounts
    (atom : Atom)
    (tokens : List RouteDescriptorPairFieldTags.Token) : Bool :=
  let counts := atom.difference.tokenCounts tokens
  atom.relation.acceptsOrdering
    (compareNats counts.1 counts.2)

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
