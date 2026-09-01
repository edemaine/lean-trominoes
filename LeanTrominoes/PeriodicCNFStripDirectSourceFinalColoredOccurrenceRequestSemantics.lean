/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalColoredOccurrenceRequestSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRequestCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceEndpointFrameSemantics

/-! # Direct semantics of aligned colored occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Declarative alignment of the exact occurrence endpoint-frame expansion
with the exact three-colored retained Figure 9 request-block stream. -/
def directSourceFinalColoredOccurrenceRequestTokensExpected
    (symbols : List encoding.Γ) :
    List DirectFinalColoredOccurrenceRequest.Token :=
  DirectFinalColoredOccurrenceRequest.output
    (directSourceFinalOccurrenceEndpointFramesExpected decider symbols)
    (directFigureNinePolarityColoredRoutedRequestBlockTokens decider symbols)

/-- The direct compiler feeds the exact declarative endpoint and routed-word
columns into the verified two-join alignment layer. -/
@[simp] theorem directSourceFinalColoredOccurrenceRequestTokens_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalColoredOccurrenceRequestTokens decider symbols =
      directSourceFinalColoredOccurrenceRequestTokensExpected
        decider symbols := by
  unfold directSourceFinalColoredOccurrenceRequestTokens
    directSourceFinalColoredOccurrenceRequestTokensExpected
  rw [directSourceFinalOccurrenceEndpointFrames_eq_expected,
    directSourceFinalColoredRoutedRequestBlockTokens_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
