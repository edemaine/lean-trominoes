/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyAllFieldStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeFieldLookupData

/-! # Representative lookup of normalized carrier source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRepresentativeFieldLookup

abbrev fieldCount : Nat :=
  CarrierSourceKeyRepresentativeFieldLookup.fieldCount

def expandedRows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  CarrierSourceKeyRepresentativeFieldLookup.expandedRows descriptors

def alignedFieldValuesAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierNormalizedSourceKeyAllFieldStream.fieldValuesWithSentinelAtPeriod
    period descriptors

def selectedFieldsAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (expandedRows descriptors).words
    (alignedFieldValuesAtPeriod period descriptors)

end CarrierNormalizedSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
