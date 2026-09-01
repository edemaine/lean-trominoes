/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockListSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairHeaderSemantics

/-! # Exact endpoint/route pairing for colored final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalColoredOccurrenceRoutePairStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private theorem map_snd_then
    {First Second Output : Type}
    (pairs : List (First × Second)) (transform : Second → Output) :
    pairs.map (fun pair => transform pair.2) =
      (pairs.map Prod.snd).map transform := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.map_cons, induction]

private theorem occurrenceFramesExpected_length_eq_routePairs
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceFramesExpected decider symbols).length =
      (directFigureNinePolarityRoutePairs decider symbols).length := by
  have headerAligned := congrArg List.length
    (directSourceFinalClauseFrames_map_header_eq_routePairs
      decider symbols)
  have clauseLength :
      (directSourceFinalClauseFrames decider symbols).length =
        (directFigureNinePolarityRoutePairs decider symbols).length := by
    simpa using headerAligned
  rw [← directSourceFinalOccurrenceFrames_eq_expected,
    directSourceFinalOccurrenceFrames_length,
    ← directSourceFinalClauseFrames_length]
  exact clauseLength

@[simp] theorem directFigureNinePolarityColoredRouteBlocks_length
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityColoredRouteBlocks decider symbols).length =
      3 * (directFigureNinePolarityRoutePairs decider symbols).length := by
  unfold directFigureNinePolarityColoredRouteBlocks
  induction directFigureNinePolarityRoutePairs decider symbols with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, induction, List.length_cons]
      omega

private theorem occurrenceEndpointFramesExpected_length_eq_routeBlocks
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceEndpointFramesExpected
        decider symbols).length =
      (directFigureNinePolarityColoredRouteBlocks
        decider symbols).length := by
  unfold directSourceFinalOccurrenceEndpointFramesExpected
  rw [DirectFinalOccurrenceEndpointFrame.output_length,
    occurrenceFramesExpected_length_eq_routePairs,
    directFigureNinePolarityColoredRouteBlocks_length]

/-- Pointwise alignment of each RGB endpoint frame with its complete routed
direction block. -/
def directSourceFinalColoredOccurrenceRoutePairs
    (symbols : List encoding.Γ) :
    List
      (DirectFinalOccurrenceEndpointFrame.Data ×
        HorizontalRoutedRouteDirectionBlock) :=
  (directSourceFinalOccurrenceEndpointFramesExpected decider symbols).zip
    (directFigureNinePolarityColoredRouteBlocks decider symbols)

@[simp] theorem directSourceFinalColoredOccurrenceRoutePairs_map_fst
    (symbols : List encoding.Γ) :
    (directSourceFinalColoredOccurrenceRoutePairs decider symbols).map
        Prod.fst =
      directSourceFinalOccurrenceEndpointFramesExpected decider symbols := by
  unfold directSourceFinalColoredOccurrenceRoutePairs
  exact List.map_fst_zip (by
    have aligned := occurrenceEndpointFramesExpected_length_eq_routeBlocks
      decider symbols
    omega)

@[simp] theorem directSourceFinalColoredOccurrenceRoutePairs_map_snd
    (symbols : List encoding.Γ) :
    (directSourceFinalColoredOccurrenceRoutePairs decider symbols).map
        Prod.snd =
      directFigureNinePolarityColoredRouteBlocks decider symbols := by
  unfold directSourceFinalColoredOccurrenceRoutePairs
  exact List.map_snd_zip (by
    have aligned := occurrenceEndpointFramesExpected_length_eq_routeBlocks
      decider symbols
    omega)

/-- The declarative colored occurrence request is the canonical paired
endpoint/route serialization. -/
theorem directSourceFinalColoredOccurrenceRequestTokensExpected_eq_paired
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceRequestTokensExpected decider symbols =
      DirectFinalColoredOccurrenceRequest.output
        ((directSourceFinalColoredOccurrenceRoutePairs
          decider symbols).map Prod.fst)
        (DirectFinalColoredOccurrenceRequest.routedSourceBlocks
          ((directSourceFinalColoredOccurrenceRoutePairs
            decider symbols).map fun pair =>
              HorizontalRoutedRouteDirectionRequest.tokens pair.2)) := by
  unfold directSourceFinalColoredOccurrenceRequestTokensExpected
  rw [directSourceFinalColoredOccurrenceRoutePairs_map_fst]
  rw [← directSourceFinalColoredRoutedRequestBlockTokens_eq]
  rw [directSourceFinalColoredRoutedRequestBlockTokens_eq_routeBlocks]
  have routeBodies :
      (directSourceFinalColoredOccurrenceRoutePairs
          decider symbols).map (fun pair =>
            HorizontalRoutedRouteDirectionRequest.tokens pair.2) =
        (directFigureNinePolarityColoredRouteBlocks
          decider symbols).map
            HorizontalRoutedRouteDirectionRequest.tokens := by
    rw [map_snd_then,
      directSourceFinalColoredOccurrenceRoutePairs_map_snd]
  rw [routeBodies]

/-- The compiled direction stream is exactly the complete delimited
occurrence-direction body for every paired endpoint frame and route block. -/
theorem directSourceFinalColoredOccurrenceDirectionTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        ((directSourceFinalColoredOccurrenceRoutePairs decider symbols).map
          fun pair =>
            HorizontalOccurrenceRoutedRequest.output
              (DirectFinalOccurrenceEndpointFrame.routedTokens
                pair.1 pair.2)) := by
  rw [directSourceFinalColoredOccurrenceDirectionTokens_eq_expected]
  unfold directSourceFinalColoredOccurrenceDirectionTokensExpected
  rw [directSourceFinalColoredOccurrenceRequestTokensExpected_eq_paired]
  exact coloredOccurrenceDirectionTokens_paired
    (directSourceFinalColoredOccurrenceRoutePairs decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
