/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestAssemblyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalContractedRouteHeaderSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalContractedDirectionTokenHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteDirectionRequestCompiler

/-! # Unconditional direct-source route-normalization request compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicThreeDM
open PeriodicThreeDM.NormalizationDirectionRequest

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

def directSourceFinalRouteDirectionRequestTokens (symbols : List encoding.Γ) : List Batch.Token :=
  Batch.RequestAssembly.output
    (directSourceFinalContractedRouteHeaders decider symbols)
    (directSourceFinalCountedContractedDirectionTokens decider symbols)

noncomputable def directSourceFinalRouteDirectionRequestTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalRouteDirectionRequestTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalRouteDirectionRequestTokens
    exact Batch.RequestAssembly.computableInPolyTimeOf id
      (directSourceFinalContractedRouteHeaders decider)
      (directSourceFinalCountedContractedDirectionTokens decider)
      (directSourceFinalContractedRouteHeadersComputableInPolyTime decider)
      (directSourceFinalCountedContractedDirectionTokensComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- The canonical request list has the same computed contracted-edge order
as the explicit header and direction compilers. -/
theorem directSparseRouteDirectionRequestsOfSymbols_eq_horizontal (symbols : List encoding.Γ) :
    directSparseRouteDirectionRequestsOfSymbols decider symbols =
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.map
        (horizontalAssembledNormalizationRequest
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  have problemEq : (directSparseComputedNormalizationInputOfSymbols decider symbols).problem =
      horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) := by
    rfl
  dsimp only [directSparseRouteDirectionRequestsOfSymbols]
  rw [← problemEq]
  apply List.map_congr_left
  intro edge member
  exact directSparse_ofEdge_eq_horizontalAssembled decider symbols edge member

/-- Header/direction joining emits the exact canonical batch encoding. -/
theorem directSourceFinalRouteDirectionRequestTokens_eq (symbols : List encoding.Γ) :
    directSourceFinalRouteDirectionRequestTokens decider symbols =
      directSparseRouteDirectionRequestTokensOfSymbols decider symbols := by
  unfold directSourceFinalRouteDirectionRequestTokens directSparseRouteDirectionRequestTokensOfSymbols
  rw [directSourceFinalContractedRouteHeaders_eq_horizontal,
    directSourceFinalCountedContractedDirectionTokens_eq_horizontal,
    directSparseRouteDirectionRequestsOfSymbols_eq_horizontal]
  have exact := Batch.RequestAssembly.output_requests
    ((horizontalThreeDMProblemComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).contractedEdges.map
      (horizontalAssembledNormalizationRequest
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)))
  simpa only [List.map_map, List.flatMap_map, Function.comp_def,
    horizontalAssembledNormalizationRequest] using exact

/-- The source-side normalization-request compiler is now an actual machine,
with no remaining header, direction, grouping, or ordering premise. -/
noncomputable def directSparseRouteDirectionRequestTokenCompiler :
    DirectSparseRouteDirectionRequestTokenCompiler decider :=
  listOutputCompiler_of_pointwise_eq id
    (directSourceFinalRouteDirectionRequestTokens decider)
    (directSparseRouteDirectionRequestTokensOfSymbols decider)
    (directSourceFinalRouteDirectionRequestTokensComputableInPolyTime decider)
    (directSourceFinalRouteDirectionRequestTokens_eq decider)

/-- All three normalization rounds therefore have an unconditional direct
source compiler for their exact final direction words and edge delimiters. -/
noncomputable def directSparseNormalizedRouteDirectionTokensOfSymbolsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSparseNormalizedRouteDirectionTokensOfSymbols decider) :=
  listOutputCompiler_of_pointwise_eq id
    (fun symbols => Batch.normalizedOutput (directSparseRouteDirectionRequestTokensOfSymbols decider symbols))
    (directSparseNormalizedRouteDirectionTokensOfSymbols decider)
    (directSparseNormalizedRouteDirectionTokensComputableInPolyTime decider
      (directSparseRouteDirectionRequestTokenCompiler decider))
    (fun symbols => Batch.normalizedOutput_tokens (directSparseRouteDirectionRequestsOfSymbols decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
