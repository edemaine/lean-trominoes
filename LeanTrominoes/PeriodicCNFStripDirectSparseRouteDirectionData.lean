/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteTripleCursor
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerRouteDirections
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerRouteStart

/-! # Finite-direction form of direct sparse route records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

open Gadget
open PeriodicCNFStripReduction

/-- Canonical assignment records streamed from a final route's affine start
and proof-free finite direction word. -/
def finalNormalizationRouteDirectionRecordBlock
    (input : Input) (edge : ContractedEdge) :
    List GadgetSparseAssignmentTokens.Token :=
  sparseRouteRecordBlocksFromDirections
    (finalNormalizationPeriod input) edge.color
    (finalNormalizationPosition input edge.toPeriodicEdge.source)
    (finalNormalizationRouteDirections input edge)

theorem finalNormalizationRouteRecordBlock_eq_directions
    (input : Input) (edge : ContractedEdge)
    (conditions : RouteDirectionConditions input edge) :
    (PeriodicCNFStripReduction.sparseRouteTriples
        (finalNormalizationRoute input edge)).flatMap
        (PeriodicCNFStripReduction.sparseRouteTripleRecordBlock
          (finalNormalizationPeriod input) edge.color) =
      finalNormalizationRouteDirectionRecordBlock input edge := by
  rw [sparseRouteRecordBlocks_eq_from_offsets]
  rw [routeStart_finalNormalizationRoute]
  rw [← map_step_finalNormalizationRouteDirections input edge conditions]
  rw [sparseRouteRecordBlocksFromOffsets_map_step]
  rfl

end NormalizationCompiler
end PeriodicThreeDM

namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteDirectionDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct edge-major route records expressed only through affine starts and
finite three-round direction streams. -/
def directSparseComputedRouteDirectionRecordsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAssignmentTokens.Token :=
  let input := directSparseComputedNormalizationInputOfSymbols decider symbols
  input.problem.contractedEdges.flatMap fun edge =>
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteDirectionRecordBlock
      input edge

/-- Pointwise route-direction certificates identify the proof-free stream
with the established canonical local-triple stream. -/
theorem directSparseComputedRouteDirectionRecordsOfSymbols_eq
    (symbols : List encoding.Γ)
    (conditions :
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      ∀ edge, edge ∈ input.problem.contractedEdges →
        PeriodicThreeDM.NormalizationCompiler.RouteDirectionConditions
          input edge) :
    directSparseComputedRouteDirectionRecordsOfSymbols decider symbols =
      directSparseComputedRouteTripleRecordsOfSymbols decider symbols := by
  unfold directSparseComputedRouteDirectionRecordsOfSymbols
    directSparseComputedRouteTripleRecordsOfSymbols
  apply List.flatMap_congr
  intro edge member
  exact
    (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRecordBlock_eq_directions
      _ edge (conditions edge member)).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
