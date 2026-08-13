/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentComputability

/-! # Computability of normalized vertex assignments -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def finalVertexRasterInput
    (input : Input × PeriodicThreeDMVertex) : Nat × Cell :=
  (finalNormalizationPeriod input.1,
    finalNormalizationPosition input.1 input.2)

theorem finalVertexRasterInput_primrec :
    Primrec finalVertexRasterInput :=
  (Primrec.pair
    (finalNormalizationPeriod_primrec.comp Primrec.fst)
    finalNormalizationPosition_primrec).of_eq fun _ => rfl

def finalVertexAssignmentInput
    (input : Input × PeriodicThreeDMVertex) :
    (Nat × Cell) × OrthogonalCellType :=
  (finalVertexRasterInput input,
    finalVertexCellType input.1 input.2)

theorem finalVertexAssignmentInput_primrec :
    Primrec finalVertexAssignmentInput :=
  (Primrec.pair finalVertexRasterInput_primrec
    finalVertexCellType_primrec).of_eq fun _ => rfl

def vertexAssignmentFromData
    (data : (Nat × Cell) × OrthogonalCellType) :
    NormalizedCellAssignment :=
  (rasterLocation data.1.1 data.1.2, data.2)

theorem vertexAssignmentFromData_primrec :
    Primrec vertexAssignmentFromData :=
  (Primrec.pair
    (rasterLocation_primrec.comp Primrec.fst)
    Primrec.snd).of_eq fun _ => rfl

def finalVertexAssignment
    (input : Input × PeriodicThreeDMVertex) :
    NormalizedCellAssignment :=
  vertexAssignmentFromData (finalVertexAssignmentInput input)

theorem finalVertexAssignment_primrec :
    Primrec finalVertexAssignment :=
  (vertexAssignmentFromData_primrec.comp
    finalVertexAssignmentInput_primrec).of_eq fun _ => rfl

theorem finalVertexAssignments_primrec :
    Primrec finalVertexAssignments := by
  have vertices : Primrec fun input : Input =>
      input.problem.contractedGraph.vertices :=
    contractedGraphVertices_primrec.comp Input.problem_primrec
  exact (Primrec.list_map vertices
    finalVertexAssignment_primrec.to₂).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
