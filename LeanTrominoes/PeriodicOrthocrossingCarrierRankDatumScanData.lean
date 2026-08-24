/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData
import LeanTrominoes.StableListRankEnumerationData

/-! # Datum-only rank-major retained carrier scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Deduplicated compiler-facing node data belonging to one carrier key. -/
def retainedCarrierRankDatumCandidates
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) : List CarrierNodeRankDatum :=
  datums.dedup.filter fun datum => datum.key = key

/-- Reconstruct one carrier's numeric node data in stable axial order by
repeated coordinate-and-presentation-index rank lookup. -/
def retainedCarrierRankDatumsByLowerRank
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) : List CarrierNodeRankDatum :=
  StableListRanks.valuesByStableLowerRank
    CarrierNodeRankDatum.orderCoordinate
    (retainedCarrierRankDatumCandidates datums key)

/-- Complete datum-only adjacent-pair scan, including crossover suppression,
zero-owner selection, and final axis/next-slice projection. -/
def retainedCarrierRankDatumBits
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  (((IndexedConsecutivePairs.pairs
      (retainedCarrierRankDatumsByLowerRank datums key)).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            pair.1.pairBits pair.2

end LeanTrominoes.PeriodicOrthocrossing
