/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexRecordData

/-! # Direct sparse vertex records from the original drawing table -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

private theorem getD_map_zipIdx_of_mem
    {Value Result : Type*}
    (values : List Value) (function : Value × Nat → Result)
    (default : Result) {tagged : Value × Nat}
    (taggedMem : tagged ∈ values.zipIdx) :
    (values.zipIdx.map function).getD tagged.2 default =
      function tagged := by
  have indexLt : tagged.2 < (values.zipIdx.map function).length := by
    simp only [List.length_map, List.length_zipIdx]
    simpa using List.snd_lt_of_mem_zipIdx taggedMem
  rw [List.getD_eq_getElem _ _ indexLt]
  simp only [List.getElem_map]
  have zipIndexLt : tagged.2 < values.zipIdx.length := by
    simpa using List.snd_lt_of_mem_zipIdx taggedMem
  have taggedAt : values.zipIdx[tagged.2]'zipIndexLt = tagged := by
    apply Prod.ext
    · simpa using (List.mem_zipIdx' taggedMem).2.symm
    · simp
  rw [taggedAt]

/-- The compiler's zip-indexed contracted position table is extensionally the
direct map of original drawing lookups over retained vertices. -/
theorem normalizationCompiler_contractedVertexPositions_eq_map
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    PeriodicThreeDM.NormalizationCompiler.contractedVertexPositions input =
      input.problem.contractedGraph.vertices.map fun vertex =>
        input.drawing.vertexPosition input.problem.incidenceGraph vertex := by
  unfold PeriodicThreeDM.NormalizationCompiler.contractedVertexPositions
  calc
    _ =
        (input.problem.contractedGraph.vertices.zipIdx.map Prod.fst).map
          (fun vertex =>
            input.drawing.vertexPosition
              input.problem.incidenceGraph vertex) := by
      rw [List.map_map]
      rfl
    _ = _ := by
      rw [List.zipIdx_map_fst]

/-- On a listed retained vertex, the stage-zero normalization lookup is just
the original input drawing's vertex lookup. -/
theorem normalizationCompiler_normalizationPosition0_eq_inputDrawing
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ input.problem.contractedGraph.vertices) :
    PeriodicThreeDM.NormalizationCompiler.normalizationPosition0
        input vertex =
      input.drawing.vertexPosition input.problem.incidenceGraph vertex := by
  have indexLt :
      input.problem.contractedGraph.vertices.idxOf vertex <
        input.problem.contractedGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr member
  have taggedMember :
      (vertex, input.problem.contractedGraph.vertices.idxOf vertex) ∈
        input.problem.contractedGraph.vertices.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨indexLt, List.idxOf_get indexLt⟩
  unfold PeriodicThreeDM.NormalizationCompiler.normalizationPosition0
    PeriodicGridDrawing.vertexPosition
    PeriodicThreeDM.NormalizationCompiler.contractedDrawing
    PeriodicThreeDM.NormalizationCompiler.contractedVertexPositions
  exact
    getD_map_zipIdx_of_mem
      input.problem.contractedGraph.vertices
      (fun tagged =>
        input.drawing.vertexPosition
          input.problem.incidenceGraph tagged.1)
      (0, 0) taggedMember

/-- Shallow affine record data using the original input drawing directly. -/
def sparseInputVertexRecordAssignment
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    Cell × OrthogonalCellType :=
  let position :=
    input.drawing.vertexPosition input.problem.incidenceGraph vertex
  let period := 1728 * input.drawing.gridSize
  (((1728 * position.1 + 471) % period,
      2 * (period : Int) - (1728 * position.2 + 471)),
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType input vertex)

theorem sparseVertexRecordAssignment_eq_input
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ input.problem.contractedGraph.vertices) :
    sparseVertexRecordAssignment input vertex =
      sparseInputVertexRecordAssignment input vertex := by
  unfold sparseVertexRecordAssignment sparseInputVertexRecordAssignment
  rw [normalizationCompiler_normalizationPosition0_eq_inputDrawing
    input member]

theorem sparseVertexRecordBlock_eq_input
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ input.problem.contractedGraph.vertices) :
    sparseVertexRecordBlock input vertex =
      GadgetSparseAssignmentTokens.assignmentTokens
        (sparseInputVertexRecordAssignment input vertex) := by
  rw [sparseVertexRecordBlock_eq_affine,
    sparseVertexRecordAssignment_eq_input input member]

theorem sparseVertexRecordBlocks_eq_inputBlocks
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedGraph.vertices.flatMap
        (sparseVertexRecordBlock input) =
      input.problem.contractedGraph.vertices.flatMap fun vertex =>
        GadgetSparseAssignmentTokens.assignmentTokens
          (sparseInputVertexRecordAssignment input vertex) := by
  apply List.flatMap_congr
  intro vertex member
  exact sparseVertexRecordBlock_eq_input input member

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseVertexInputDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct vertex records can be generated from original drawing lookups,
without constructing the contracted drawing's derived position list. -/
theorem directSparseComputedVertexRecordsOfSymbols_eq_inputBlocks
    (symbols : List encoding.Γ) :
    directSparseComputedVertexRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedGraph.vertices.flatMap fun vertex =>
        GadgetSparseAssignmentTokens.assignmentTokens
          (sparseInputVertexRecordAssignment input vertex) := by
  rw [directSparseComputedVertexRecordsOfSymbols_eq_blocks]
  exact sparseVertexRecordBlocks_eq_inputBlocks _

end PeriodicCNFStripReduction
end LeanTrominoes
