/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingCanonicalOccurrencePairPredicateData

/-! # Numeric CNF crossing occurrence-pair enumeration -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- Neighboring translated segment occurrences reconstructed from the compact
numeric segment stream. -/
def numericNeighborOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (IndexedGridSegment × Cell) :=
  (numericIndexedSegments formula).flatMap fun indexed =>
    neighborTranslations.map fun translate =>
      (indexed, translate)

/-- Ordered occurrence pairs retained by the graph-free canonical crossing
predicate at a supplied numeric period. -/
def numericOrientedCrossingOccurrencePairsAtPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (period : Nat) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  (numericNeighborOccurrences formula ×ˢ
      numericNeighborOccurrences formula).filter
    (canonicalOrientedOccurrencePairAtPeriod period)

/-- Numeric crossing-pair scan at the formula's exact orthocrossing period. -/
def numericOrientedCrossingOccurrencePairs
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  numericOrientedCrossingOccurrencePairsAtPeriod formula
    (drawingGridSize formula.incidenceGraph)

end PeriodicCNF
end LeanTrominoes
