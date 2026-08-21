/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPairScanNodup
import Mathlib.Data.List.ProdSigma

/-! # Direct occurrence-pair scan for canonical crossings -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The crossing-candidate stream is the image of the ordered neighboring
segment-occurrence product. -/
theorem crossingHaloCandidates_eq_map_occurrenceProduct
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    crossingHaloCandidates graph =
      ((neighborOccurrences graph ×ˢ neighborOccurrences graph).map fun pair =>
        orientedCrossingCandidate graph pair.1 pair.2) := by
  have flatMap_eq
      (firsts seconds : List (IndexedGridSegment × Cell)) :
      (firsts.flatMap fun first => seconds.map fun second =>
        orientedCrossingCandidate graph first second) =
        ((firsts ×ˢ seconds).map fun pair =>
          orientedCrossingCandidate graph pair.1 pair.2) := by
    induction firsts with
    | nil => rfl
    | cons first firsts induction =>
        simp [List.product_cons, induction, List.map_map,
          Function.comp_def]
  unfold crossingHaloCandidates
  exact flatMap_eq _ _

/-- Predicate checked directly on an ordered pair of neighboring segment
occurrences, before allocating its crossing record. -/
def canonicalOrientedOccurrencePair
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) × (IndexedGridSegment × Cell)) : Bool :=
  let record := orientedCrossingCandidate graph pair.1 pair.2
  decide (record.IsCanonical graph ∧
    (record.firstSegment graph).IsHorizontal)

/-- Dedup-free canonical crossing scan retaining occurrence pairs instead of
allocating crossing records. -/
def orientedCrossingOccurrencePairs
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List ((IndexedGridSegment × Cell) × (IndexedGridSegment × Cell)) :=
  (neighborOccurrences graph ×ˢ neighborOccurrences graph).filter
    (canonicalOrientedOccurrencePair graph)

/-- Mapping the retained occurrence pairs constructs exactly the previously
verified filtered crossing-record stream. -/
theorem orientedCrossingPairFilter_eq_map_occurrencePairs
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    orientedCrossingPairFilter graph =
      (orientedCrossingOccurrencePairs graph).map fun pair =>
        orientedCrossingCandidate graph pair.1 pair.2 := by
  unfold orientedCrossingPairFilter orientedCrossingOccurrencePairs
    canonicalOrientedOccurrencePair
  rw [crossingHaloCandidates_eq_map_occurrenceProduct]
  induction neighborOccurrences graph ×ˢ neighborOccurrences graph with
  | nil => rfl
  | cons pair pairs induction =>
      by_cases canonical :
          (orientedCrossingCandidate graph pair.1 pair.2).IsCanonical graph
      · by_cases horizontal :
          ((orientedCrossingCandidate graph pair.1 pair.2).firstSegment
            graph).IsHorizontal
        · simp [canonical, horizontal, induction]
        · simp [canonical, horizontal, induction]
      · simp [canonical, induction]

/-- The direct occurrence-pair scan has exactly the semantic filtered crossing
count. -/
theorem orientedCrossingOccurrencePairs_length_eq_pairFilter
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (orientedCrossingOccurrencePairs graph).length =
      (orientedCrossingPairFilter graph).length := by
  rw [orientedCrossingPairFilter_eq_map_occurrencePairs]
  simp

end PeriodicOrthocrossing
end LeanTrominoes
