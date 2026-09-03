/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRoutePairSemantics

/-! # Occurrence blocks of direct colored direction bodies -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM

/-- The three complete routed direction bodies determined by one occurrence
endpoint frame and its aligned retained Figure 9 header/tail pair. -/
def directFinalOccurrenceDirectionBodyBlock
    (frame : DirectFinalOccurrenceFrame.Data)
    (pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection) :
    List (List AxisDirection) :=
  incidenceColors.map fun color =>
    HorizontalOccurrenceRoutedRequest.output
      (DirectFinalOccurrenceEndpointFrame.routedTokens
        (DirectFinalOccurrenceEndpointFrame.ofColor frame color)
        (HorizontalRoutedRouteHeader.block pair.1 pair.2))

private theorem coloredDirectionBodies_zip_blocks
    (frames : List DirectFinalOccurrenceFrame.Data)
    (pairs : List
      (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    (((DirectFinalOccurrenceEndpointFrame.output frames).zip
        (pairs.flatMap fun pair =>
          List.replicate 3
            (HorizontalRoutedRouteHeader.block pair.1 pair.2))).map
      fun pair =>
        HorizontalOccurrenceRoutedRequest.output
          (DirectFinalOccurrenceEndpointFrame.routedTokens
            pair.1 pair.2)) =
      (List.zipWith directFinalOccurrenceDirectionBodyBlock
        frames pairs).flatten := by
  induction frames generalizing pairs with
  | nil => rfl
  | cons frame frames induction =>
      cases pairs with
      | nil => rfl
      | cons pair pairs =>
          simp [DirectFinalOccurrenceEndpointFrame.output,
            DirectFinalOccurrenceEndpointFrame.frameBlock,
            incidenceColors, directFinalOccurrenceDirectionBodyBlock]
          simpa [DirectFinalOccurrenceEndpointFrame.output,
            directFinalOccurrenceDirectionBodyBlock] using induction pairs

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The flat clause-major colored body column is exactly the flattening of
one explicit RGB direction-body block per final occurrence. -/
theorem directSourceFinalColoredOccurrenceDirectionBodies_eq_occurrenceBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceDirectionBodies decider symbols =
      (List.zipWith directFinalOccurrenceDirectionBodyBlock
        (directSourceFinalOccurrenceFramesExpected decider symbols)
        (directFigureNinePolarityRoutePairs decider symbols)).flatten := by
  unfold directSourceFinalColoredOccurrenceDirectionBodies
    directSourceFinalColoredOccurrenceRoutePairs
    directSourceFinalOccurrenceEndpointFramesExpected
    directFigureNinePolarityColoredRouteBlocks
  exact coloredDirectionBodies_zip_blocks _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
