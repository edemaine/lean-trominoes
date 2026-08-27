/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteTripleCursor

/-! # Exact-offset form of the direct sparse route records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteOffsetDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct route-record suffix represented edge by edge by the first
route cell and its exact coordinate-offset stream. -/
def directSparseComputedRouteOffsetRecordsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAssignmentTokens.Token :=
  let input := directSparseComputedNormalizationInputOfSymbols decider symbols
  input.problem.contractedEdges.flatMap fun edge =>
    let route :=
      PeriodicThreeDM.NormalizationCompiler.finalNormalizationRoute input edge
    sparseRouteRecordBlocksFromOffsets
      (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod input)
      edge.color (routeStart route) (routeStepOffsets route)

/-- This proof-free offset target is exactly the canonical edge-major local
triple record word. -/
theorem directSparseComputedRouteOffsetRecordsOfSymbols_eq
    (symbols : List encoding.Γ) :
    directSparseComputedRouteOffsetRecordsOfSymbols decider symbols =
      directSparseComputedRouteTripleRecordsOfSymbols decider symbols := by
  unfold directSparseComputedRouteOffsetRecordsOfSymbols
    directSparseComputedRouteTripleRecordsOfSymbols
  dsimp only
  apply List.flatMap_congr
  intro edge _
  symm
  exact sparseRouteRecordBlocks_eq_from_offsets _ _ _

end PeriodicCNFStripReduction
end LeanTrominoes

end
