/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectFinalColoredOccurrenceRequestSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Colored.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRequestCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceEndpointFrameSemantics

/-! # Direct semantics of aligned colored occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

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
