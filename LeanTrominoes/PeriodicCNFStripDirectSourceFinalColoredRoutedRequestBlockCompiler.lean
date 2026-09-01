/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EndDelimitedBlockFixedCopiesCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRoutedRequestBlockCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Three colored copies of every direct final routed request block -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace DirectFinalColoredRoutedRequestBlock

open Computability Turing

abbrev Token := HorizontalRoutedRouteHeaderTailBlock.Token

def isEnd : Token → Bool
  | .requestEnd => true
  | .request _ => false

/-- Repeat each complete routed-request block for red, green, and blue. -/
def copied (source : List Token) : List Token :=
  EndDelimitedBlockFixedCopies.copiedTokens 3 isEnd source

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id copied :=
  EndDelimitedBlockFixedCopies.computableInPolyTime 3 isEnd

end DirectFinalColoredRoutedRequestBlock

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalColoredRoutedRequestStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One complete routed-request block for every colored final occurrence. -/
def directSourceFinalColoredRoutedRequestBlockTokens
    (symbols : List encoding.Γ) :
    List DirectFinalColoredRoutedRequestBlock.Token :=
  DirectFinalColoredRoutedRequestBlock.copied
    (directSourceFinalCompiledRoutedRequestBlockTokens decider symbols)

/-- Canonical semantic target obtained by applying the same color expansion
to the retained Figure 9 routed-request blocks. -/
def directFigureNinePolarityColoredRoutedRequestBlockTokens
    (symbols : List encoding.Γ) :
    List DirectFinalColoredRoutedRequestBlock.Token :=
  DirectFinalColoredRoutedRequestBlock.copied
    (directFigureNinePolarityRoutedRequestBlockTokens decider symbols)

/-- The compiled colored block stream is exactly the canonical retained
Figure 9 stream with each request repeated three times. -/
@[simp] theorem directSourceFinalColoredRoutedRequestBlockTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalColoredRoutedRequestBlockTokens decider symbols =
      directFigureNinePolarityColoredRoutedRequestBlockTokens
        decider symbols := by
  unfold directSourceFinalColoredRoutedRequestBlockTokens
    directFigureNinePolarityColoredRoutedRequestBlockTokens
  rw [directSourceFinalCompiledRoutedRequestBlockTokens_eq]

/-- Colored routed-request blocks are polynomial-time computable directly
from the source symbols. -/
noncomputable def
    directSourceFinalColoredRoutedRequestBlockTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalColoredRoutedRequestBlockTokens decider) := by
  unfold directSourceFinalColoredRoutedRequestBlockTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCompiledRoutedRequestBlockTokensComputableInPolyTime
      decider)
    DirectFinalColoredRoutedRequestBlock.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
