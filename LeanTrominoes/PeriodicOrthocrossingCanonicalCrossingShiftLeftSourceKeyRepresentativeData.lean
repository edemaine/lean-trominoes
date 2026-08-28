/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamData

/-! # Stable representatives of common-shift source-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentatives

open RouteDescriptorOccurrenceSlotBinaryWords
open PaddedSupportedLastRepresentativeEqualityRows

/-- The complete fixed candidate list produced from one descriptor stream. -/
def candidateList (descriptors : List RouteDescriptor) :
    List (Candidate CarrierNodeSourceKeys.SourceKeyPair) :=
  CanonicalCrossingShiftLeftSourceKeyStream.candidates
    (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

/-- Guarded candidate words followed by the explicit rejection sentinel. -/
def wordsWithSentinel (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  PaddedSupportedCandidateWords.wordsWithSentinel
    CarrierNodeSourceKeys.word (candidateList descriptors)

/-- Equality rows at the last occurrence of every active compact source
pair. -/
def representativeRows (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  PaddedSupportedCandidateWords.representativeRows
    CarrierNodeSourceKeys.word (candidateList descriptors)

/-- The semantic compact source-pair list selected by those rows. -/
def values (descriptors : List RouteDescriptor) :
    List CarrierNodeSourceKeys.SourceKeyPair :=
  ((candidateList descriptors).filterMap Candidate.value).dedup

/-- Guarded presentation of the selected source pairs. -/
def guardedWords (descriptors : List RouteDescriptor) :
    List (List Bool) :=
  (values descriptors).map fun sourcePair =>
    true :: CarrierNodeSourceKeys.word sourcePair

end CanonicalCrossingShiftLeftSourceKeyRepresentatives
end LeanTrominoes.PeriodicOrthocrossing
