/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRequestCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestDelimitedBatchCompiler

/-! # Direct final colored occurrence-direction block compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    directFinalColoredOccurrenceDirectionBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

abbrev DirectFinalColoredOccurrenceDirectionToken :=
  HorizontalOccurrenceRoutedRequest.DelimitedBatch.Token

/-- One end-delimited direction block per final occurrence and color, in
occurrence-major and red/green/blue-minor order. -/
def directSourceFinalColoredOccurrenceDirectionTokens
    (symbols : List encoding.Γ) :
    List DirectFinalColoredOccurrenceDirectionToken :=
  HorizontalOccurrenceRoutedRequest.DelimitedBatch.output
    (directSourceFinalColoredOccurrenceRequestTokens decider symbols)

noncomputable def
    directSourceFinalColoredOccurrenceDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalColoredOccurrenceDirectionTokens decider) := by
  unfold directSourceFinalColoredOccurrenceDirectionTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalColoredOccurrenceRequestTokensComputableInPolyTime
      decider)
    HorizontalOccurrenceRoutedRequest.DelimitedBatch.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
