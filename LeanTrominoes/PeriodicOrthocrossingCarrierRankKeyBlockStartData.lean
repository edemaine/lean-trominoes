/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyBlockStartValidity

/-! # Per-occurrence carrier-key block starts -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyBlockStarts

def lookupInput (descriptors : List RouteDescriptor) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := CarrierRankKeyEqualityRows.semanticRows descriptors
  values := CarrierRankKeyContributionStarts.starts descriptors
  valid := CarrierRankKeyBlockStartValidity.valid descriptors

/-- Start of the last-occurrence-ordered key block containing each compact
carrier datum. -/
def starts (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (CarrierRankKeyEqualityRows.semanticRows descriptors)
    (CarrierRankKeyContributionStarts.starts descriptors)

end CarrierRankKeyBlockStarts
end LeanTrominoes.PeriodicOrthocrossing
