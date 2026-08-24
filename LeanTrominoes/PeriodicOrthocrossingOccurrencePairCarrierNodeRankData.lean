/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierOrderData
import LeanTrominoes.StrictListRanks

/-! # Graph-free ranks of retained carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Candidate nodes on one retained physical carrier before geometric
sorting.  This names the exact deduplicated and key-filtered presentation
already consumed by `retainedCompleteCarrierNodesAtPeriod`. -/
def retainedCarrierNodeCandidatesAtPeriod
    (nodes : List CarrierNode) (key : Nat × Nat × Cell) :
    List CarrierNode :=
  nodes.dedup.filter fun node => node.carrierKey = key

/-- A retained candidate node's geometric rank, computed by counting
same-carrier candidates at a lower axial coordinate. -/
def retainedCarrierNodeLowerRankAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) (node : CarrierNode) : Nat :=
  StrictListRanks.lowerRank
    (carrierNodeOrderCoordinateAtPeriod period)
    (retainedCarrierNodeCandidatesAtPeriod nodes key) node

end LeanTrominoes.PeriodicOrthocrossing
