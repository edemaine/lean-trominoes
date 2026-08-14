/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentComputability
import LeanTrominoes.PeriodicThreeDMNormalizationVertexAssignmentComputability

/-! # Primitive-recursive final rectangular assignments -/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def finalStripVertexAssignment
    (input : Input × PeriodicThreeDMVertex) :
    NormalizedCellAssignment :=
  (stripRasterLocation (finalNormalizationPeriod input.1)
      (finalNormalizationPosition input.1 input.2),
    finalVertexCellType input.1 input.2)

theorem finalStripVertexAssignment_primrec :
    Primrec finalStripVertexAssignment := by
  have locationInput : Primrec fun
      input : Input × PeriodicThreeDMVertex =>
        (finalNormalizationPeriod input.1,
          finalNormalizationPosition input.1 input.2) :=
    Primrec.pair
      (finalNormalizationPeriod_primrec.comp Primrec.fst)
      finalNormalizationPosition_primrec
  exact (Primrec.pair
    (stripRasterLocation_primrec.comp locationInput)
    finalVertexCellType_primrec).of_eq fun _ => rfl

theorem finalStripVertexAssignments_primrec :
    Primrec finalStripVertexAssignments := by
  have vertices : Primrec fun input : Input =>
      input.problem.contractedGraph.vertices :=
    contractedGraphVertices_primrec.comp Input.problem_primrec
  exact (Primrec.list_map vertices
    finalStripVertexAssignment_primrec.to₂).of_eq fun _ => rfl

def finalStripRouteAssignmentInput
    (input : Input × ContractedEdge) :
    StripRouteInteriorAssignmentsInput :=
  ((finalNormalizationPeriod input.1, input.2.color),
    finalNormalizationRoute input.1 input.2)

theorem finalStripRouteAssignmentInput_primrec :
    Primrec finalStripRouteAssignmentInput :=
  (Primrec.pair
    (Primrec.pair
      (finalNormalizationPeriod_primrec.comp Primrec.fst)
      (contractedEdge_color_primrec.comp Primrec.snd))
    finalNormalizationRoute_primrec).of_eq fun _ => rfl

def finalStripRouteAssignmentsForEdge
    (input : Input × ContractedEdge) :
    List NormalizedCellAssignment :=
  stripRouteInteriorAssignments
    (finalStripRouteAssignmentInput input).1.1
    (finalStripRouteAssignmentInput input).1.2
    (finalStripRouteAssignmentInput input).2

theorem finalStripRouteAssignmentsForEdge_primrec :
    Primrec finalStripRouteAssignmentsForEdge :=
  (stripRouteInteriorAssignments_primrec.comp
    finalStripRouteAssignmentInput_primrec).of_eq fun _ => rfl

theorem finalStripRouteAssignments_primrec :
    Primrec finalStripRouteAssignments := by
  have edges : Primrec fun input : Input =>
      input.problem.contractedEdges :=
    contractedEdges_primrec.comp Input.problem_primrec
  exact (Primrec.list_flatMap edges
    finalStripRouteAssignmentsForEdge_primrec.to₂).of_eq fun _ => rfl

theorem finalStripCellAssignments_primrec :
    Primrec finalStripCellAssignments :=
  (Primrec.list_append.comp finalStripVertexAssignments_primrec
    finalStripRouteAssignments_primrec).of_eq fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
