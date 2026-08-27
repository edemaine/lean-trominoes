/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedAssignmentData
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchCompiler

/-! # Direct batches of finite route-normalization requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM.NormalizationDirectionRequest

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteDirectionRequestDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One exact finite normalization request per contracted edge, in the same
stable order as the canonical route-record suffix. -/
def directSparseRouteDirectionRequestsOfSymbols
    (symbols : List encoding.Γ) : List Request :=
  let input := directSparseComputedNormalizationInputOfSymbols decider symbols
  input.problem.contractedEdges.map fun edge => ofEdge input edge

def directSparseRouteDirectionRequestTokensOfSymbols
    (symbols : List encoding.Γ) : List Batch.Token :=
  Batch.tokens
    (directSparseRouteDirectionRequestsOfSymbols decider symbols)

/-- Normalized batch output for the direct request stream. -/
def directSparseNormalizedRouteDirectionTokensOfSymbols
    (symbols : List encoding.Γ) : List Batch.NormalizedToken :=
  Batch.normalizedTokens
    (directSparseRouteDirectionRequestsOfSymbols decider symbols)

/-- The batch semantics are exactly one final direction word and delimiter
per executable contracted edge. -/
theorem directSparseNormalizedRouteDirectionTokensOfSymbols_eq
    (symbols : List encoding.Γ) :
    directSparseNormalizedRouteDirectionTokensOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedEdges.flatMap fun edge =>
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteDirections
          input edge).map
            Batch.NormalizedToken.direction ++
          [Batch.NormalizedToken.routeEnd] := by
  unfold directSparseNormalizedRouteDirectionTokensOfSymbols
    directSparseRouteDirectionRequestsOfSymbols
    Batch.normalizedTokens Batch.normalizedBlock
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro edge _
  rw [normalizeThreeRounds_ofEdge_directions]

end PeriodicCNFStripReduction
end LeanTrominoes

end
