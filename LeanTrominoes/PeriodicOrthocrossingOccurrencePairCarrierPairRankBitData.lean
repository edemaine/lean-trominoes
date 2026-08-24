/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierBitData

/-! # Representative carrier bits from rank-major endpoint pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Zero-owner representative carrier pairs selected from the rank-major
adjacent-pair stream. -/
def retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (CarrierNode × CarrierNode) :=
  (retainedCarrierNodePairsByLowerRankAtPeriod period nodes key).filter
    (CarrierNodePairIsRepresentativeAtPeriod period)

/-- Exact axis and next-slice bit projection of the rank-major representative
carrier-pair stream. -/
def retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  (retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod
    period nodes key).map fun pair =>
      (pair.1.isHorizontal,
        carrierNodePairNextSliceAtPeriod period pair)

end LeanTrominoes.PeriodicOrthocrossing
