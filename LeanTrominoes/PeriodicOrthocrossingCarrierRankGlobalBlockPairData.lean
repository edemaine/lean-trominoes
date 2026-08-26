/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationData

/-! # Retained pairs inside global carrier-rank blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Project adjacent globally indexed entries in one semantic carrier block
back to their two rank data. -/
def keyBlockDatumPairs (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) :
    List (CarrierNodeRankDatum × CarrierNodeRankDatum) :=
  (IndexedConsecutivePairs.pairs
    (keyBlock datums (CarrierRankCompiledKey.ofKey key))).map fun pair =>
      (pair.1.1, pair.2.1)

/-- Crossover suppression, representative selection, and bit projection over
one globally ranked carrier block. -/
def keyBlockBits (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) : List (Bool × Bool) :=
  (((keyBlockDatumPairs datums key).filter fun pair =>
      !pair.1.sameCrossoverSite pair.2).filter fun pair =>
        pair.1.pairIsRepresentative pair.2).map fun pair =>
          pair.1.pairBits pair.2

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
