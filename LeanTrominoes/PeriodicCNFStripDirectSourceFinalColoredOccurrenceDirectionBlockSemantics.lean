/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalColoredOccurrenceRequestSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRequestSemantics

/-! # Semantics of direct final colored occurrence-direction blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalColoredOccurrenceDirectionTokensExpected
    (symbols : List encoding.Γ) :
    List DirectFinalColoredOccurrenceDirectionToken :=
  HorizontalOccurrenceRoutedRequest.DelimitedBatch.output
    (directSourceFinalColoredOccurrenceRequestTokensExpected
      decider symbols)

@[simp] theorem
    directSourceFinalColoredOccurrenceDirectionTokens_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceDirectionTokens decider symbols =
      directSourceFinalColoredOccurrenceDirectionTokensExpected
        decider symbols := by
  unfold directSourceFinalColoredOccurrenceDirectionTokens
    directSourceFinalColoredOccurrenceDirectionTokensExpected
  rw [directSourceFinalColoredOccurrenceRequestTokens_eq_expected]

/-- On an explicit alignment, the delimiter-preserving compiler emits one
complete exact direction block for every colored occurrence. -/
@[simp] theorem coloredOccurrenceDirectionTokens_paired
    (pairs : List
      (DirectFinalOccurrenceEndpointFrame.Data ×
        HorizontalRoutedRouteDirectionBlock)) :
    HorizontalOccurrenceRoutedRequest.DelimitedBatch.output
        (DirectFinalColoredOccurrenceRequest.output
          (pairs.map Prod.fst)
          (DirectFinalColoredOccurrenceRequest.routedSourceBlocks
            (pairs.map fun pair =>
              HorizontalRoutedRouteDirectionRequest.tokens pair.2))) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (pairs.map fun pair =>
          HorizontalOccurrenceRoutedRequest.output
            (DirectFinalOccurrenceEndpointFrame.routedTokens
              pair.1 pair.2)) := by
  rw [DirectFinalColoredOccurrenceRequest.output_canonicalPairs,
    HorizontalOccurrenceRoutedRequest.DelimitedBatch.output_blocks]
  rw [List.map_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
