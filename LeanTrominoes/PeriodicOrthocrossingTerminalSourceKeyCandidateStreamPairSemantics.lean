/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyGuardedWordPairSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamData

/-! # Paired source-key words of the padded terminal-node stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

theorem componentWords_paddedTerminalCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (paddedTerminalCarrierNodeCandidateStream descriptors)) =
      ⟨TerminalSourceKeyRecipeStream.guardedWords
        (descriptors ×ˢ descriptors)⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold CarrierNodeSourceKeyCandidateWords.componentPairs
    paddedTerminalCarrierNodeCandidateStream
    TerminalSourceKeyRecipeStream.guardedWords
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair _pairMember
  have pairEq := congrArg DelimitedBinaryWords.Input.words
    (componentWords_terminalCandidates pair)
  simpa [DelimitedBinaryWordGuardedPairMerge.componentWords,
    CarrierNodeSourceKeyCandidateWords.componentPairs] using pairEq

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
