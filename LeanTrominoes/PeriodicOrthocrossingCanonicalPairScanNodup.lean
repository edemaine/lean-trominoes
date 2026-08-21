/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingIndexedSegmentsNodup
import LeanTrominoes.PeriodicOrthocrossingCanonicalPairScan
import Mathlib.Data.List.ProdSigma

/-! # Duplicate freedom of the canonical crossing pair scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Dedup-free executable form of the canonical oriented pair scan. -/
def orientedCrossingPairFilter
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  ((crossingHaloCandidates graph).filter fun record =>
    record.IsCanonical graph).filter fun record =>
      (record.firstSegment graph).IsHorizontal

theorem neighborOccurrences_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (neighborOccurrences graph).Nodup := by
  change (((drawing graph).indexedSegments ×ˢ
    neighborTranslations)).Nodup
  exact (PeriodicGridDrawing.indexedSegments_nodup _).product
    neighborTranslations_nodup

theorem crossingHaloCandidates_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (crossingHaloCandidates graph).Nodup := by
  have pairsNodup :
      (neighborOccurrences graph ×ˢ neighborOccurrences graph).Nodup :=
    (neighborOccurrences_nodup graph).product
      (neighborOccurrences_nodup graph)
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
  rw [flatMap_eq]
  apply pairsNodup.map
  intro first second equal
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg CrossingRecord.first equal
    · exact congrArg CrossingRecord.firstTranslate equal
  · apply Prod.ext
    · exact congrArg CrossingRecord.second equal
    · exact congrArg CrossingRecord.secondTranslate equal

/-- The two crossing predicates preserve duplicate freedom, so the final
`dedup` in the semantic pair scan is executable but redundant. -/
theorem orientedCrossingPairScan_eq_filters
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    orientedCrossingPairScan graph =
      orientedCrossingPairFilter graph := by
  unfold orientedCrossingPairScan orientedCrossingPairFilter
  apply List.dedup_eq_self.mpr
  exact ((crossingHaloCandidates_nodup graph).filter _).filter _

end PeriodicOrthocrossing
end LeanTrominoes
