/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRequestCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRoutedRequestBatchCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct final colored occurrence-direction compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalColoredOccurrenceDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Concatenated routed directions for all colored final occurrences. -/
def directSourceFinalColoredOccurrenceDirections
    (symbols : List encoding.Γ) : List AxisDirection :=
  HorizontalOccurrenceRoutedRequest.Batch.output
    (directSourceFinalColoredOccurrenceRequestTokens decider symbols)

/-- The complete colored occurrence-direction stream is polynomial-time
computable from the direct source symbols. -/
noncomputable def
    directSourceFinalColoredOccurrenceDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalColoredOccurrenceDirections decider) := by
  unfold directSourceFinalColoredOccurrenceDirections
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalColoredOccurrenceRequestTokensComputableInPolyTime
      decider)
    HorizontalOccurrenceRoutedRequest.Batch.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
