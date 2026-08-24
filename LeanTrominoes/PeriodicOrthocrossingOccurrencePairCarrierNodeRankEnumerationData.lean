/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankLookupData
import LeanTrominoes.StrictListRankEnumerationData

/-! # Retained carrier chains reconstructed by geometric ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Enumerate one retained carrier's nodes by repeated lower-coordinate rank
lookup over the original graph-free presentation. -/
def retainedCarrierNodesByLowerRankAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List CarrierNode :=
  StrictListRanks.valuesByLowerRank
    (carrierNodeOrderCoordinateAtPeriod period)
    (retainedCarrierNodeCandidatesAtPeriod nodes key)

/-- Adjacent non-crossover carrier pairs reconstructed from the rank-major
node enumeration. -/
def retainedCarrierNodePairsByLowerRankAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (CarrierNode × CarrierNode) :=
  (IndexedConsecutivePairs.pairs
    (retainedCarrierNodesByLowerRankAtPeriod period nodes key)).filter
      fun pair => !pair.1.sameCrossoverSite pair.2

end LeanTrominoes.PeriodicOrthocrossing
