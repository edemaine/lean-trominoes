/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionData
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyAllFieldStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Representative carrier source-key field lookup data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRepresentativeFieldLookup

open PaddedSupportedLastRepresentativeEqualityRows

def fieldCount : Nat := 12

/-- Twelve numeric fields of one optional compact source-key pair. -/
def sourcePairFields :
    Option CarrierNodeSourceKeys.SourceKeyPair → List Nat
  | none => List.replicate fieldCount 0
  | some sourcePair =>
      CarrierKeyAllFieldProjector.keyFields (some sourcePair.1) ++
        CarrierKeyAllFieldProjector.keyFields (some sourcePair.2)

/-- Candidate-major source-key fields and their final rejection sentinel. -/
def alignedFieldValues (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyAllFieldStream.fieldValuesWithSentinel descriptors

/-- Repeat each representative equality row once for every source-key
field, selecting one fixed position in each copy. -/
def expandedRows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordFixedFieldRowExpansion.rows fieldCount
    (paddedCarrierSourceKeyRepresentativeRows descriptors)

/-- Physical fixed-field lookup result. -/
def selectedFields (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (expandedRows descriptors).words (alignedFieldValues descriptors)

/-- Semantic twelve-field blocks in stable compact-source-key dedup order. -/
def semanticFields (descriptors : List RouteDescriptor) : List Nat :=
  ((paddedCarrierSourceKeyCandidateStream descriptors).filterMap
    Candidate.value).dedup.flatMap fun sourcePair =>
      sourcePairFields (some sourcePair)

end CarrierSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
