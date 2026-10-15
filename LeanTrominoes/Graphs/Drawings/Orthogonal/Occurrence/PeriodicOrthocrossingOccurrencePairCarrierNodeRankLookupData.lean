/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Occurrence.PeriodicOrthocrossingOccurrencePairCarrierNodeRankData
import LeanTrominoes.Common.List.StrictListRankLookupData

/-! # Graph-free carrier-node lookup by geometric rank -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Select a retained same-key carrier node directly from its axial rank,
without sorting the presented carrier-node stream. -/
def retainedCarrierNodeAtLowerRank?
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) (rank : Nat) : Option CarrierNode :=
  StrictListRanks.valueAtLowerRank?
    (carrierNodeOrderCoordinateAtPeriod period)
    (retainedCarrierNodeCandidatesAtPeriod nodes key) rank

end LeanTrominoes.PeriodicOrthocrossing
