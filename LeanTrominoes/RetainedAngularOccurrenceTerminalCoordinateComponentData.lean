/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComparisonComponents
import LeanTrominoes.SignedUnaryStrictLowerCompiler
import LeanTrominoes.UnaryFieldEqualityRowsCompiler

/-! # Numeric component data for retained terminal coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace TerminalCoordinateComponents

open PeriodicThreeSATThree

/-- Ordinary pairs underlying all retained terminal coordinates, in global
occurrence-presentation order. -/
def coordinates
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    List (Nat × Nat) :=
  (allOccurrenceVariables source).map fun copy =>
    ofLex (retainedOccurrenceTerminalCoordinate routes copy)

/-- Finite angular ranks projected from a terminal-coordinate stream. -/
def directionRanks (coordinates : List (Nat × Nat)) : List Nat :=
  coordinates.map Prod.fst

/-- Radial primitive-block lengths projected from a terminal-coordinate
stream. -/
def radialLengths (coordinates : List (Nat × Nat)) : List Nat :=
  coordinates.map Prod.snd

/-- Row-major strict lexicographic comparison assembled from direction-rank
strict order, direction-rank equality, and radial strict order. -/
def strictLowerBits (coordinates : List (Nat × Nat)) : List Bool :=
  SignedUnaryStrictLower.pairwise .disjunction
    (UnaryFieldStrictLowerRows.strictLowerBits
      (directionRanks coordinates))
    (SignedUnaryStrictLower.pairwise .conjunction
      (UnaryFieldEqualityRows.equalityBits
        (directionRanks coordinates))
      (UnaryFieldStrictLowerRows.strictLowerBits
        (radialLengths coordinates)))

/-- Row-major equality assembled from equality of both numeric coordinate
components. -/
def equalityBits (coordinates : List (Nat × Nat)) : List Bool :=
  SignedUnaryStrictLower.pairwise .conjunction
    (UnaryFieldEqualityRows.equalityBits
      (directionRanks coordinates))
    (UnaryFieldEqualityRows.equalityBits
      (radialLengths coordinates))

end TerminalCoordinateComponents
end PeriodicEightOccurrenceSplit
end LeanTrominoes
