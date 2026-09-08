/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSelectedIncidenceBodyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalContractedDirectionTokenSemantics
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # The compiled contraction emits the actual geometric direction stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicThreeDM

private opaque listOutputCompiler_of_pointwise_eq
    {Domain InputSymbol OutputSymbol : Type}
    (encodeInput : Domain → List InputSymbol)
    (first second : Domain → List OutputSymbol)
    (compiler : TM2ComputableInPolyTime encodeInput id first)
    (equal : ∀ input, first input = second input) :
    TM2ComputableInPolyTime encodeInput id second := by
  exact @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    Domain (List OutputSymbol) (List OutputSymbol) InputSymbol OutputSymbol
    encodeInput id id first second compiler equal

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every delimited compiled route word is the actual geometric word at the
same canonical contracted-edge position. -/
theorem directSourceFinalCountedContractedDirectionTokens_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCountedContractedDirectionTokens decider symbols =
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.flatMap
        (fun edge => NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
          (horizontalAssembledContractedDirections
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) edge)) := by
  rw [directSourceFinalCountedContractedDirectionTokens_eq_edgeBlocks,
    directSourceFinalCountedContractedEdgeBlocks_eq_horizontal]
  exact horizontalContractedDirectionBlocks_outputTokens _ _
    (horizontalCanonicalIncidenceDirectionBlocks_correct _)

/-- The existing explicit machine therefore emits the complete canonical
geometric route-word stream in polynomial time. -/
noncomputable def horizontalAssembledContractedDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id (fun symbols : List encoding.Γ =>
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.flatMap
        (fun edge => NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
          (horizontalAssembledContractedDirections
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) edge))) := by
  exact listOutputCompiler_of_pointwise_eq id
    (directSourceFinalCountedContractedDirectionTokens decider)
    (fun symbols : List encoding.Γ =>
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.flatMap
        (fun edge => NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
          (horizontalAssembledContractedDirections
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) edge)))
    (@directSourceFinalCountedContractedDirectionTokensComputableInPolyTime
      Input encoding language decider)
    (@directSourceFinalCountedContractedDirectionTokens_eq_horizontal
      Input encoding language decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
