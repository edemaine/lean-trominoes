/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderTailCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiled compact requests from direct Figure 9 route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompiledRoutedRequestStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Canonical compact routed-request tokens obtained from the retained Figure
9 header/tail record list. -/
def directFigureNinePolarityRoutedRequestTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteDirectionRequest.Token :=
  HorizontalRoutedRouteHeaderTail.output
    (directFigureNinePolarityRouteTailRecords decider symbols)

/-- Apply the fixed header/tail streaming pass to the compiled direct record
stream. -/
def directSourceFinalCompiledRoutedRequestTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteDirectionRequest.Token :=
  HorizontalRoutedRouteHeaderTail.output
    (directSourceFinalCompiledRouteTailRecords decider symbols)

/-- The complete compact routed-request stream is polynomial-time computable
from direct source symbols. -/
noncomputable def
    directSourceFinalCompiledRoutedRequestTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCompiledRoutedRequestTokens decider) := by
  unfold directSourceFinalCompiledRoutedRequestTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledRouteTailRecordsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderTail.computableInPolyTime

/-- The compiled request tokens are exactly the canonical retained Figure 9
routed requests. -/
@[simp] theorem directSourceFinalCompiledRoutedRequestTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCompiledRoutedRequestTokens decider symbols =
      directFigureNinePolarityRoutedRequestTokens decider symbols := by
  unfold directSourceFinalCompiledRoutedRequestTokens
    directFigureNinePolarityRoutedRequestTokens
  rw [directSourceFinalCompiledRouteTailRecords_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
