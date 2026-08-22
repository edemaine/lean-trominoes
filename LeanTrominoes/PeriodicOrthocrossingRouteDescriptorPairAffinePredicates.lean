/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressions

/-! # Boolean predicates over affine route-descriptor pair expressions -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The four integer comparisons needed by the route and crossing guards. -/
inductive Relation
  | equal
  | notEqual
  | less
  | lessEqual
  deriving DecidableEq, Fintype

/-- Boolean interpretation of one integer comparison. -/
def Relation.eval : Relation → Int → Int → Bool
  | .equal, first, second => decide (first = second)
  | .notEqual, first, second => decide (first ≠ second)
  | .less, first, second => decide (first < second)
  | .lessEqual, first, second => decide (first ≤ second)

/-- One comparison between two fixed affine expressions. -/
structure Atom where
  relation : Relation
  first : Expression
  second : Expression
  deriving DecidableEq

/-- Evaluate one comparison under a natural-valued field assignment. -/
def Atom.eval
    (valuation : Side → Fin 11 → Nat) (atom : Atom) : Bool :=
  atom.relation.eval (atom.first.eval valuation) (atom.second.eval valuation)

/-- A fixed Boolean formula over affine comparisons. -/
inductive Predicate
  | truth
  | falsity
  | atom (comparison : Atom)
  | conjunction (first second : Predicate)
  | disjunction (first second : Predicate)
  | negation (input : Predicate)
  deriving DecidableEq

/-- Evaluate a fixed affine predicate under a field assignment. -/
def Predicate.eval
    (valuation : Side → Fin 11 → Nat) : Predicate → Bool
  | .truth => true
  | .falsity => false
  | .atom comparison => comparison.eval valuation
  | .conjunction first second => first.eval valuation && second.eval valuation
  | .disjunction first second => first.eval valuation || second.eval valuation
  | .negation input => !(input.eval valuation)

/-- Evaluate a predicate on the semantic fields of a descriptor pair. -/
def Predicate.evalPair
    (predicate : Predicate) (pair : RouteDescriptor × RouteDescriptor) : Bool :=
  predicate.eval (pairFieldValue pair)

/-- Evaluate a predicate by counting tagged unary units. -/
def Predicate.evalTokens
    (predicate : Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) : Bool :=
  predicate.eval (tokenFieldValue tokens)

/-- A constant affine expression. -/
def constant (value : Int) : Expression :=
  ⟨value, []⟩

/-- The natural value of one selected pair field, viewed as an integer. -/
def field (side : Side) (position : Fin 11) : Expression :=
  ⟨0, [term 1 side position]⟩

/-- Compare two affine expressions. -/
def compare
    (relation : Relation) (first second : Expression) : Predicate :=
  .atom ⟨relation, first, second⟩

/-- Affine equality. -/
def equal (first second : Expression) : Predicate :=
  compare .equal first second

/-- Affine disequality. -/
def notEqual (first second : Expression) : Predicate :=
  compare .notEqual first second

/-- Strict affine inequality. -/
def less (first second : Expression) : Predicate :=
  compare .less first second

/-- Nonstrict affine inequality. -/
def lessEqual (first second : Expression) : Predicate :=
  compare .lessEqual first second

/-- Conjoin a fixed list of predicates. -/
def all : List Predicate → Predicate
  | [] => .truth
  | predicate :: predicates => .conjunction predicate (all predicates)

/-- Disjoin a fixed list of predicates. -/
def any : List Predicate → Predicate
  | [] => .falsity
  | predicate :: predicates => .disjunction predicate (any predicates)

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
