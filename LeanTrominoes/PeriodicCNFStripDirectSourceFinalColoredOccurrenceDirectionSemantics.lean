/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRequestSemantics

/-! # Semantics of direct final colored occurrence directions -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Declarative direction stream obtained by compiling the exact aligned
endpoint and three-colored Figure 9 route columns. -/
def directSourceFinalColoredOccurrenceDirectionsExpected
    (symbols : List encoding.Γ) : List AxisDirection :=
  HorizontalOccurrenceRoutedRequest.Batch.output
    (directSourceFinalColoredOccurrenceRequestTokensExpected decider symbols)

@[simp] theorem directSourceFinalColoredOccurrenceDirections_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceDirections decider symbols =
      directSourceFinalColoredOccurrenceDirectionsExpected
        decider symbols := by
  unfold directSourceFinalColoredOccurrenceDirections
    directSourceFinalColoredOccurrenceDirectionsExpected
  rw [directSourceFinalColoredOccurrenceRequestTokens_eq_expected]

/-- On an explicit alignment, batched compilation independently emits the
established routed-occurrence result for every frame/route pair. -/
@[simp] theorem coloredOccurrenceDirections_paired
    (pairs : List
      (DirectFinalOccurrenceEndpointFrame.Data ×
        HorizontalRoutedRouteDirectionBlock)) :
    HorizontalOccurrenceRoutedRequest.Batch.output
        (DirectFinalColoredOccurrenceRequest.output
          (pairs.map Prod.fst)
          (DirectFinalColoredOccurrenceRequest.routedSourceBlocks
            (pairs.map fun pair =>
              HorizontalRoutedRouteDirectionRequest.tokens pair.2))) =
      pairs.flatMap fun pair =>
        HorizontalOccurrenceRoutedRequest.output
          (DirectFinalOccurrenceEndpointFrame.routedTokens
            pair.1 pair.2) := by
  rw [DirectFinalColoredOccurrenceRequest.output_canonicalPairs,
    HorizontalOccurrenceRoutedRequest.Batch.output_blocks]
  simp [List.flatMap_map]

end LeanTrominoes.PeriodicCNFStripReduction

end
