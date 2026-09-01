/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalColoredOccurrenceRequestData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics

/-! # Explicit colored Figure 9 routed-block list -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalColoredRoutedBlockListStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Actual routed direction blocks in occurrence-major/color-minor order. -/
def directFigureNinePolarityColoredRouteBlocks
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteDirectionBlock :=
  (directFigureNinePolarityRoutePairs decider symbols).flatMap fun pair =>
    List.replicate 3
      (HorizontalRoutedRouteHeader.block pair.1 pair.2)

/-- The physical colored request stream is canonical serialization of the
explicit RGB routed-block list. -/
theorem directSourceFinalColoredRoutedRequestBlockTokens_eq_routeBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalColoredRoutedRequestBlockTokens decider symbols =
      DirectFinalColoredOccurrenceRequest.routedSourceBlocks
        ((directFigureNinePolarityColoredRouteBlocks decider symbols).map
          HorizontalRoutedRouteDirectionRequest.tokens) := by
  rw [directSourceFinalColoredRoutedRequestBlockTokens_eq_blocks]
  unfold directFigureNinePolarityColoredRouteBlocks
    DirectFinalColoredOccurrenceRequest.routedSourceBlocks
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pair pairMember
  rw [List.flatMap_map]
  change
    EndDelimitedBlockFixedCopies.copiedBlock 3
        (DirectFinalColoredOccurrenceRequest.routedSourceBlock
          (HorizontalRoutedRouteDirectionRequest.tokens
            (HorizontalRoutedRouteHeader.block pair.1 pair.2))) =
      (List.replicate 3
        (HorizontalRoutedRouteHeader.block pair.1 pair.2)).flatMap
          (fun block =>
            DirectFinalColoredOccurrenceRequest.routedSourceBlock
              (HorizontalRoutedRouteDirectionRequest.tokens block))
  exact EndDelimitedBlockFixedCopies.copiedBlock_eq_replicate_flatMap
    3 (HorizontalRoutedRouteHeader.block pair.1 pair.2)
      (fun block =>
        DirectFinalColoredOccurrenceRequest.routedSourceBlock
          (HorizontalRoutedRouteDirectionRequest.tokens block))

end LeanTrominoes.PeriodicCNFStripReduction

end
