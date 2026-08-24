/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionData

/-! # Graph-free ordering of retained occurrence-pair carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- All reconstructed retained nodes on one physical carrier, deduplicated and
sorted using only the explicit drawing period. -/
def retainedCompleteCarrierNodesAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List CarrierNode :=
  (nodes.dedup.filter fun node =>
      node.carrierKey = key).insertionSort fun first second =>
    carrierNodeOrderCoordinateAtPeriod period first ≤
      carrierNodeOrderCoordinateAtPeriod period second

/-- Adjacent retained node pairs on one physical carrier, omitting the
internal pair across a single crossover site. -/
def retainedCompleteCarrierNodePairsAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (CarrierNode × CarrierNode) :=
  (consecutivePairs
      (retainedCompleteCarrierNodesAtPeriod period nodes key)).filter
    fun pair => !pair.1.sameCrossoverSite pair.2

end LeanTrominoes.PeriodicOrthocrossing
