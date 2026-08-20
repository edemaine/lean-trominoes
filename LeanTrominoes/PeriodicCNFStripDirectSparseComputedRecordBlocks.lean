/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedRecordSplit

/-! # Per-object blocks of direct sparse assignment records -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- The single canonical assignment record contributed by one contracted
vertex. -/
def sparseVertexRecordBlock
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentTokens
    (PeriodicThreeDM.stripRasterLocation
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod input)
        (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPosition
          input vertex),
      PeriodicThreeDM.NormalizationCompiler.finalVertexCellType input vertex)

/-- Canonical records contributed by the interior of one contracted edge's
final normalized route. -/
def sparseRouteRecordBlock
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (edge : PeriodicThreeDM.ContractedEdge) :
    List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentsTokens
    (PeriodicThreeDM.stripRouteInteriorAssignments
      (PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod input)
      edge.color
      (PeriodicThreeDM.NormalizationCompiler.finalNormalizationRoute input edge))

theorem vertexRecords_eq_flatMap
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    GadgetSparseAssignmentTokens.assignmentsTokens
        (PeriodicThreeDM.NormalizationCompiler.finalStripVertexAssignments
          input) =
      input.problem.contractedGraph.vertices.flatMap
        (sparseVertexRecordBlock input) := by
  unfold PeriodicThreeDM.NormalizationCompiler.finalStripVertexAssignments
    sparseVertexRecordBlock
  rw [GadgetSparseAssignmentTokens.assignmentsTokens_map]

theorem routeRecords_eq_flatMap
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    GadgetSparseAssignmentTokens.assignmentsTokens
        (PeriodicThreeDM.NormalizationCompiler.finalStripRouteAssignments
          input) =
      input.problem.contractedEdges.flatMap (sparseRouteRecordBlock input) := by
  unfold PeriodicThreeDM.NormalizationCompiler.finalStripRouteAssignments
    sparseRouteRecordBlock
  rw [GadgetSparseAssignmentTokens.assignmentsTokens_flatMap]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseComputedRecordBlockStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

@[simp] theorem directSparseComputedVertexRecordsOfSymbols_eq_blocks
    (symbols : List encoding.Γ) :
    directSparseComputedVertexRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedGraph.vertices.flatMap
        (sparseVertexRecordBlock input) := by
  unfold directSparseComputedVertexRecordsOfSymbols
  exact vertexRecords_eq_flatMap _

@[simp] theorem directSparseComputedRouteRecordsOfSymbols_eq_blocks
    (symbols : List encoding.Γ) :
    directSparseComputedRouteRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedEdges.flatMap
        (sparseRouteRecordBlock input) := by
  unfold directSparseComputedRouteRecordsOfSymbols
  exact routeRecords_eq_flatMap _

end PeriodicCNFStripReduction
end LeanTrominoes
