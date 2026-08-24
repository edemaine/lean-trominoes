/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierPairRankBitData

/-! # Rank-major carrier bits over compiler-facing node data -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Project the rank-major carrier-node stream to numeric data, form adjacent
pairs, suppress crossover-internal pairs, retain zero-shift owners, and emit
their two finite metadata bits. -/
def retainedCarrierRankDatumBitsAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  let datums :=
    (retainedCarrierNodesByLowerRankAtPeriod period nodes key).map
      (carrierNodeRankDatumAtPeriod period)
  (((IndexedConsecutivePairs.pairs datums).filter fun pair =>
      !pair.1.sameCrossoverSite pair.2).filter fun pair =>
        pair.1.pairIsRepresentative pair.2).map fun pair =>
          pair.1.pairBits pair.2

end LeanTrominoes.PeriodicOrthocrossing
