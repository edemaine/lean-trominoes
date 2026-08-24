/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationData

/-! # Graph-free retained carrier-pair bits -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Ordered axis and next-slice bits of the representative adjacent-node
pairs in one reconstructed physical carrier block. -/
def retainedRepresentativeCarrierPairBitsAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  (retainedRepresentativeCarrierNodePairsAtPeriod
    period nodes key).map fun pair =>
      (pair.1.isHorizontal,
        carrierNodePairNextSliceAtPeriod period pair)

end LeanTrominoes.PeriodicOrthocrossing
