/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerData

/-! # Pointwise predicates used by stable carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierRankStableLower

def lowerPredicate
    (first second : CarrierNodeRankDatum) : Bool :=
  decide (first.key = second.key) &&
    decide (second.orderCoordinate < first.orderCoordinate)

def tiePredicate
    (first second : CarrierNodeRankDatum) : Bool :=
  decide (first.key = second.key) &&
    decide (first.orderCoordinate = second.orderCoordinate)

end LeanTrominoes.PeriodicOrthocrossing.CarrierRankStableLower
