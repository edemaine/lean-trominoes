/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankCompiledKeyInjectiveSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalNumericSemantics
import LeanTrominoes.StrictListRankEnumerationData

/-! # Semantic enumeration by global carrier rank -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

def datumKey (datum : CarrierNodeRankDatum) : CarrierRankCompiledKey :=
  CarrierRankCompiledKey.ofDatum datum

def entryKey (entry : CarrierNodeRankDatum × Nat) :
    CarrierRankCompiledKey :=
  datumKey entry.1

def selectedKey (key : CarrierRankCompiledKey)
    (datum : CarrierNodeRankDatum) : Bool :=
  decide (datumKey datum = key)

/-- Stable coordinate enumeration of the globally indexed data belonging to
one aggregate carrier key. -/
def keyBlock (datums : List CarrierNodeRankDatum)
    (key : CarrierRankCompiledKey) : List (CarrierNodeRankDatum × Nat) :=
  StrictListRanks.valuesByLowerRank
    (StableListRanks.indexedCoordinate
      CarrierNodeRankDatum.orderCoordinate)
    (datums.zipIdx.filter fun entry => selectedKey key entry.1)

/-- All indexed carrier data in dedup-last key order and stable coordinate
order within each key. -/
def enumeration (datums : List CarrierNodeRankDatum) :
    List (CarrierNodeRankDatum × Nat) :=
  (datums.map CarrierRankCompiledKey.ofDatum).dedup.flatMap
    (keyBlock datums)

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
