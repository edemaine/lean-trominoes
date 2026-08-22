/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValues

/-! # Affine expressions over tagged route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- One signed multiple of one unary field in an ordered descriptor pair. -/
structure Term where
  coefficient : Int
  side : Side
  field : Fin 11
  deriving DecidableEq

/-- A fixed signed affine expression over the twenty-two unary pair fields. -/
structure Expression where
  constant : Int
  terms : List Term
  deriving DecidableEq

/-- Interpret one affine term under a natural-valued field assignment. -/
def Term.eval
    (valuation : Side → Fin 11 → Nat) (term : Term) : Int :=
  term.coefficient * (valuation term.side term.field : Int)

/-- Interpret an affine expression under a natural-valued field assignment. -/
def Expression.eval
    (valuation : Side → Fin 11 → Nat) (expression : Expression) : Int :=
  expression.constant + (expression.terms.map (Term.eval valuation)).sum

/-- Interpret an expression in the semantic fields of a descriptor pair. -/
def Expression.evalPair
    (expression : Expression) (pair : RouteDescriptor × RouteDescriptor) : Int :=
  expression.eval (pairFieldValue pair)

/-- Interpret an expression by physically counting tagged unary units. -/
def Expression.evalTokens
    (expression : Expression) (tokens : List RouteDescriptorPairFieldTags.Token) :
    Int :=
  expression.eval (tokenFieldValue tokens)

/-- The descriptor selected by one side of an ordered pair. -/
def descriptorAt
    (pair : RouteDescriptor × RouteDescriptor) : Side → RouteDescriptor
  | .first => pair.1
  | .second => pair.2

/-- A compact constructor for one field term. -/
def term (coefficient : Int) (side : Side) (field : Fin 11) : Term :=
  ⟨coefficient, side, field⟩

/-- The drawing period `16 * (vertexCount + edgeCount + 1)`. -/
def gridSize (side : Side) : Expression :=
  ⟨16, [term 16 side 0, term 16 side 1]⟩

/-- The source port column `8 * sourceVertexIndex + 2 * sourcePortRank + 2`. -/
def sourcePortX (side : Side) : Expression :=
  ⟨2, [term 8 side 3, term 2 side 5]⟩

/-- The target port column `8 * targetVertexIndex + 2 * targetPortRank + 2`. -/
def targetPortX (side : Side) : Expression :=
  ⟨2, [term 8 side 4, term 2 side 6]⟩

/-- The private low track row `6 + 4 * edgeIndex`. -/
def lowTrack (side : Side) : Expression :=
  ⟨6, [term 4 side 2]⟩

/-- The private high track row `7 + 4 * edgeIndex`. -/
def highTrack (side : Side) : Expression :=
  ⟨7, [term 4 side 2]⟩

/-- The vertical gate column `4 + 8 * vertexCount + 2 * edgeIndex`. -/
def gateX (side : Side) : Expression :=
  ⟨4, [term 8 side 0, term 2 side 2]⟩

/-- Signed horizontal lattice offset reconstructed from fields seven and eight. -/
def horizontalOffset (side : Side) : Expression :=
  ⟨0, [term 1 side 7, term (-1) side 8]⟩

/-- Signed vertical lattice offset reconstructed from fields nine and ten. -/
def verticalOffset (side : Side) : Expression :=
  ⟨0, [term 1 side 9, term (-1) side 10]⟩

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
