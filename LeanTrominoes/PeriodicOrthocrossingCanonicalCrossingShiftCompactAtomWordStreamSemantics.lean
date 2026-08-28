/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCompactAtomWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftCompactAtomWordStreamData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagSemantics

/-! # Semantics of common-shift compact crossover atom-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftCompactAtomWordStream

open RouteDescriptorOccurrenceSlotBinaryWords
open PaddedSupportedLastRepresentativeEqualityRows

private theorem crossoverWords_map_guardedWord_eq_filterMap
    (candidateList : List (Candidate CarrierNodeSourceKeys.SourceKeyPair))
    (supportEq : ∀ candidate ∈ candidateList,
      candidate.supported = candidate.value.isSome) :
    CrossoverCompactAtomWords.words
        (candidateList.map
          (PaddedSupportedCandidateWords.guardedWord
            CarrierNodeSourceKeys.word)) =
      (candidateList.filterMap Candidate.value).flatMap fun sourcePair =>
        CrossoverCompactAtomWords.wordsForRoles
          (true :: CarrierNodeSourceKeys.word sourcePair) := by
  induction candidateList with
  | nil => rfl
  | cons candidate candidateList induction =>
      have headSupport := supportEq candidate (by simp)
      have tailSupport : ∀ other ∈ candidateList,
          other.supported = other.value.isSome := by
        intro other member
        exact supportEq other (by simp [member])
      rw [List.map_cons]
      change CrossoverCompactAtomWords.wordsForRoles
          (PaddedSupportedCandidateWords.guardedWord
            CarrierNodeSourceKeys.word candidate) ++
          CrossoverCompactAtomWords.words
            (candidateList.map
              (PaddedSupportedCandidateWords.guardedWord
                CarrierNodeSourceKeys.word)) = _
      rw [induction tailSupport, List.filterMap_cons]
      rcases candidate with ⟨value, supported⟩
      cases value with
      | none =>
          simp at headSupport
          simp [headSupport, PaddedSupportedCandidateWords.guardedWord,
            CrossoverCompactAtomWords.wordsForRoles,
            CrossoverCompactAtomWords.word]
      | some value =>
          simp at headSupport
          simp [headSupport, PaddedSupportedCandidateWords.guardedWord,
          CrossoverCompactAtomWords.wordsForRoles,
          CrossoverCompactAtomWords.word]

private theorem sourceKeyCandidates_supported_eq_isSome
    (pairs : List (TaggedDescriptor × TaggedDescriptor)) :
    ∀ candidate ∈
        CanonicalCrossingShiftLeftSourceKeyStream.candidates pairs,
      candidate.supported = candidate.value.isSome := by
  intro candidate candidateMember
  unfold CanonicalCrossingShiftLeftSourceKeyStream.candidates at candidateMember
  rcases List.mem_flatMap.mp candidateMember with
    ⟨pair, _pairMember, candidateMember⟩
  unfold RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyCandidates
    at candidateMember
  rcases List.mem_map.mp candidateMember with
    ⟨nodeCandidate, _nodeCandidateMember, candidateEq⟩
  subst candidate
  rcases nodeCandidate with ⟨value, supported⟩
  cases value <;>
    rfl

@[simp] theorem sourceTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    sourceTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode ⟨guardedSourceWords descriptors⟩ := by
  unfold sourceTokens guardedSourceWords
  rw [expandedPairs_descriptorWords,
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens_wordPairs,
    CanonicalCrossingShiftLeftSourceKeyStream.emittedStream_encodeDescriptorSlotPairs]

@[simp] theorem emittedTokens_descriptorWords
    (descriptors : List RouteDescriptor) :
    emittedTokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode (input descriptors) := by
  unfold emittedTokens input words
  rw [sourceTokens_descriptorWords,
    CrossoverCompactAtomWords.tokens_encode]
  rfl

/-- At the semantic boundary, the fixed expander removes precisely the
inactive padded candidates and expands every active source pair. -/
theorem words_eq_activeSourcePairBlocks
    (descriptors : List RouteDescriptor) :
    words descriptors =
      ((CanonicalCrossingShiftLeftSourceKeyStream.candidates
        (taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors)).filterMap Candidate.value).flatMap
        fun sourcePair => CrossoverCompactAtomWords.wordsForRoles
          (true :: CarrierNodeSourceKeys.word sourcePair) := by
  unfold words guardedSourceWords
  rw [CanonicalCrossingShiftLeftSourceKeyStream.guardedWords_eq_candidates]
  exact crossoverWords_map_guardedWord_eq_filterMap _
    (sourceKeyCandidates_supported_eq_isSome _)

/-- The emitted active blocks are exactly the Figure 8(b) atom words of the
physical common-shift crossing-record scan. -/
theorem words_eq_occurrencePairShiftScan
    {Variable : Type*}
    (sourceWord : Variable → List Bool)
    (period : Nat) (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonPeriod :
      ∀ descriptor ∈ descriptors, descriptor.gridSize = period)
    (localShapes :
      ∀ descriptor ∈ descriptors,
        RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape
          descriptor) :
    words descriptors =
      (occurrencePairCanonicalCrossingRecordShiftScanAtPeriod period
        (routeDescriptorNeighborOccurrences descriptors)).flatMap
          fun crossing =>
            PlanarThreeSAT.crossoverFormula.flatMap fun clause =>
              clause.literals.map fun literal =>
                RetainedCompactAtomWords.word sourceWord
                  ⟨normalizedCrossoverAtom crossing literal.1⟩ := by
  rw [words_eq_activeSourcePairBlocks]
  rw [CanonicalCrossingShiftLeftSourceKeyStream.filterMap_candidates_eq_occurrencePairShiftScan
    period descriptors selfIndexed commonPeriod localShapes]
  unfold occurrencePairCanonicalLeftSourceKeyShiftScanAtPeriod
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro crossing _crossingMember
  exact CrossoverCompactAtomWords.wordsForRoles_crossingPair
    sourceWord crossing

end CanonicalCrossingShiftCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing
