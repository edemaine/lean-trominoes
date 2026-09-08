/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairFirstCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierKeyCompactAtomWordCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyCandidateStreamPairSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamSemantics

/-! # Compact keys aligned with the active physical terminal-coordinate stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCompactKeys

open Computability Turing RouteDescriptorPairAffine
open PaddedSupportedLastRepresentativeEqualityRows

/-- The compact terminal constructor followed by the physical first source key. -/
def nodeWord (node : CarrierNode) : List Bool :=
  [false, false] ++ CarrierKeyWords.word (CarrierNodeSourceKeys.pair node).1

/-- Retain one component per guarded pair, remove sentinels, and retag active keys. -/
def words (descriptors : List RouteDescriptor) : DelimitedBinaryWords.Input :=
  GuardedCarrierKeyCompactAtomWords.compact
    (DelimitedBinaryWordPairFirst.first
      ⟨TerminalSourceKeyRecipeStream.guardedWords (descriptors ×ˢ descriptors)⟩)

private def tokens (input : DelimitedBinaryWords.Input) : List DelimitedBinaryWords.Token :=
  GuardedCarrierKeyCompactAtomWords.tokens (DelimitedBinaryWordPairFirst.tokens
    (TerminalSourceKeyRecipeStream.emittedStream (CarrierKeyRecipeStream.terminalTags input)))

private noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id tokens := by
  unfold tokens
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (TM2CompositionMachine.computableInPolyTime
        CarrierKeyRecipeStream.terminalTagsComputableInPolyTime
        TerminalSourceKeyRecipeStream.emittedStreamComputableInPolyTime)
      DelimitedBinaryWordPairFirst.tokensComputableInPolyTime)
    GuardedCarrierKeyCompactAtomWords.tokensComputableInPolyTime

private theorem tokens_descriptorWords (descriptors : List RouteDescriptor) :
    tokens (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode (words descriptors) := by
  unfold tokens words
  rw [CarrierKeyRecipeStream.terminalTags_descriptorWords,
    TerminalSourceKeyRecipeStream.emittedStream_encodeDescriptorPairs,
    DelimitedBinaryWordPairFirst.tokens_encode,
    GuardedCarrierKeyCompactAtomWords.tokens_encode]

/-- The physical terminal dictionary keys are polynomial-time computable
from the same descriptor words as their coordinate columns. -/
noncomputable def wordsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode (RouteDescriptorBinaryWords.words descriptors))
      DelimitedBinaryWords.finEncoding.encode words := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words tokensComputableInPolyTime
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared tokens_descriptorWords

private theorem compact_componentPairs (candidates : List (Candidate CarrierNode)) :
    (GuardedCarrierKeyCompactAtomWords.compact
      (DelimitedBinaryWordPairFirst.first
        (DelimitedBinaryWordGuardedPairMerge.componentWords
          (CarrierNodeSourceKeyCandidateWords.componentPairs candidates)))).words =
      (candidates.filterMap Candidate.value).map nodeWord := by
  rw [DelimitedBinaryWordPairFirst.first_componentWords]
  unfold GuardedCarrierKeyCompactAtomWords.compact
    GuardedCarrierKeyCompactAtomWords.words CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [List.map_map]
  dsimp only
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      cases valueEq : candidate.value <;>
        simp [CarrierNodeSourceKeyCandidateWords.componentPair, valueEq,
          GuardedCarrierKeyCompactAtomWords.word, PaddedSupportedCandidateWords.sentinelWord,
          nodeWord, induction]

/-- Keys and coordinate values use exactly the same active padded-candidate order. -/
theorem words_eq_activeNodes (descriptors : List RouteDescriptor) :
    (words descriptors).words =
      ((paddedTerminalCarrierNodeCandidateStream descriptors).filterMap Candidate.value).map
        nodeWord := by
  unfold words
  rw [← componentWords_paddedTerminalCarrierNodeCandidateStream]
  exact compact_componentPairs _

/-- On actual source routes, one key is emitted for each physical endpoint in
neighboring-segment order. -/
theorem words_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable] (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) (forward : formula.IsForwardLocal) :
    (words (PeriodicCNF.numericRouteDescriptors formula)).words =
      ((routeDescriptorNeighborOccurrences (PeriodicCNF.numericRouteDescriptors formula)).flatMap
        occurrenceCarrierTerminalNodes).map nodeWord := by
  rw [words_eq_activeNodes, paddedTerminalCarrierNodeCandidateStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward]

end LeanTrominoes.PeriodicOrthocrossing.ActiveTerminalCompactKeys

end
