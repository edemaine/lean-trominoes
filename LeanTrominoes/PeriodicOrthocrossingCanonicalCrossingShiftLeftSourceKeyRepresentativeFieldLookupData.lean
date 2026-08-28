/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionData
import LeanTrominoes.LastTrueUnaryValueLookupMachine
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyAllFieldStreamData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeData

/-! # Representative lookup of canonical crossing source-pair fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup

open RouteDescriptorOccurrenceSlotBinaryWords

def fieldCount : Nat := 12

/-- Give every source-pair representative row one row per reconstructed
source-pair field. -/
def expandedRows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordFixedFieldRowExpansion.rows fieldCount
    (CanonicalCrossingShiftLeftSourceKeyRepresentatives.representativeRows
      descriptors)

/-- Candidate-major source-pair fields aligned with the expanded rows. -/
def alignedFieldValues (descriptors : List RouteDescriptor) : List Nat :=
  CanonicalCrossingShiftLeftSourceKeyAllFieldStream.fieldValuesWithSentinel
    (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

/-- The twelve fields carried by one optional compact source-key pair. -/
def sourcePairFields :
    Option CarrierNodeSourceKeys.SourceKeyPair → List Nat
  | none =>
      CarrierKeyAllFieldProjector.keyFields none ++
        CarrierKeyAllFieldProjector.keyFields none
  | some sourcePair =>
      CarrierKeyAllFieldProjector.keyFields (some sourcePair.1) ++
        CarrierKeyAllFieldProjector.keyFields (some sourcePair.2)

/-- Expected selected field stream of the stable compact source pairs. -/
def semanticFields (descriptors : List RouteDescriptor) : List Nat :=
  (CanonicalCrossingShiftLeftSourceKeyRepresentatives.values descriptors).flatMap
    fun sourcePair => sourcePairFields (some sourcePair)

/-- The twelve source-pair fields selected at each stable representative. -/
def selectedFields (descriptors : List RouteDescriptor) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (expandedRows descriptors).words (alignedFieldValues descriptors)

end CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup
end LeanTrominoes.PeriodicOrthocrossing
