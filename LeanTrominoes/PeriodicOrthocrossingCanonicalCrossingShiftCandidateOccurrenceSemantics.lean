/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCandidateValueSemantics

/-! # Physical-occurrence semantics of common-shift candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorPairAffine

/-- Under the two selected local shapes, compacted shifted-slot candidates
are exactly the fixed physical common-shift block at the two runtime slots.
An inactive padded occurrence slot contributes no candidate. -/
theorem filterMap_canonicalCrossingShiftLeftSourceKeyCandidates_eq_occurrenceBlock_of_matches
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    (canonicalCrossingShiftLeftSourceKeyCandidates pair).filterMap
        Candidate.value =
      match occurrenceAtSlot pair.1, occurrenceAtSlot pair.2 with
      | some first, some second =>
          occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
            pair.1.1.gridSize (first, second)
      | _, _ => [] := by
  rw [
    filterMap_canonicalCrossingShiftLeftSourceKeyCandidates_eq_shiftCandidates_of_matches
      firstShape secondShape pair firstMatches secondMatches]
  cases firstAt : occurrenceAtSlot pair.1 with
  | none =>
      simp [canonicalShiftCandidateAtPeriod, firstAt]
  | some first =>
      cases secondAt : occurrenceAtSlot pair.2 with
      | none =>
          simp [canonicalShiftCandidateAtPeriod, firstAt, secondAt]
      | some second =>
          simp only [canonicalShiftCandidateAtPeriod, firstAt, secondAt]
          unfold occurrencePairCanonicalLeftSourceKeyShiftBlockAtPeriod
            occurrencePairCanonicalCrossingRecordShiftBlockAtPeriod
            occurrencePairCanonicalShiftCandidatesAtPeriod
          rw [List.filterMap_map]
          induction carrierCrossingRetentionShifts with
          | nil => rfl
          | cons shift shifts induction =>
              simp only [List.filterMap_cons, Function.comp_apply]
              cases occurrencePairCanonicalShiftCandidateAtPeriod
                  pair.1.1.gridSize (first, second) shift <;>
                simp [induction]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
