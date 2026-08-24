/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Rank-datum field lookup through compact carrier identities -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumLookup

open PaddedSupportedLastRepresentativeEqualityRows

/-- Reconstruct one natural-valued rank-datum field from an optional
reversible carrier identity.  Inactive padded slots carry zero. -/
def fieldValueAtPeriod (period : Nat)
    (field : CarrierNodeRankDatum → Nat) : Option CarrierNodeCode → Nat
  | none => 0
  | some code => field (carrierNodeRankDatumAtPeriod period code.node)

/-- One aligned field per padded identity slot, followed by the lookup
sentinel aligned with every representative row's rejection bit. -/
def fieldValuesWithSentinelAtPeriod (period : Nat)
    (descriptors : List RouteDescriptor)
    (field : CarrierNodeRankDatum → Nat) : List Nat :=
  (values (paddedCarrierIdentityCandidateStreamAtPeriod
    period descriptors)).map (fieldValueAtPeriod period field) ++ [0]

/-- Look up a natural-valued rank-datum field at every compact source-key
representative row. -/
def selectedFieldValuesAtPeriod (period : Nat)
    (descriptors : List RouteDescriptor)
    (field : CarrierNodeRankDatum → Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (paddedCarrierSourceKeyRepresentativeRows descriptors).words
    (fieldValuesWithSentinelAtPeriod period descriptors field)

end CarrierRankDatumLookup
end LeanTrominoes.PeriodicOrthocrossing
