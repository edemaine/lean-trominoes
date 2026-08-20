/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexRecordAffineBounds
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerVertexBounds

/-! # Fundamental-square bounds for direct sparse vertex records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseVertexDirectBoundsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The executable direct input inherits the semantic presentation's full
fundamental-square bounds. -/
theorem directSparseComputedInput_vertexPosition_bounds
    (symbols : List encoding.Γ)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ (directSparseComputedNormalizationInputOfSymbols
      decider symbols).problem.contractedGraph.vertices) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    let position := input.drawing.vertexPosition
      input.problem.incidenceGraph vertex
    0 ≤ position.1 ∧ position.1 < (input.drawing.gridSize : Int) ∧
      0 ≤ position.2 ∧ position.2 < (input.drawing.gridSize : Int) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  have inputEq :
      directSparseComputedNormalizationInputOfSymbols decider symbols =
        normalizationInput source := by
    exact directSparseComputedNormalizationInputOfSymbols_eq decider symbols
  rw [inputEq] at member ⊢
  exact
    normalizationCompiler_inputOfPresentation_vertexPosition_bounds
      ((presentation source).toPlanarPresentation) member

/-- Horizontal projection of the direct input's full coordinate bounds. -/
theorem directSparseComputedInput_vertexPosition_horizontal_bounds
    (symbols : List encoding.Γ)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ (directSparseComputedNormalizationInputOfSymbols
      decider symbols).problem.contractedGraph.vertices) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).1 ∧
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).1 <
        (input.drawing.gridSize : Int) := by
  have bounds :=
    directSparseComputedInput_vertexPosition_bounds decider symbols member
  exact ⟨bounds.1, bounds.2.1⟩

/-- Every direct vertex record therefore uses modulus-free affine coordinate
fields. -/
theorem directSparseComputedVertexRecordsOfSymbols_eq_boundedBlocks
    (symbols : List encoding.Γ) :
    directSparseComputedVertexRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedGraph.vertices.flatMap fun vertex =>
        GadgetSparseAssignmentTokens.assignmentTokens
          (sparseBoundedInputVertexRecordAssignment input vertex) := by
  rw [directSparseComputedVertexRecordsOfSymbols_eq_inputBlocks]
  dsimp only
  apply List.flatMap_congr
  intro vertex member
  have bounds :=
    directSparseComputedInput_vertexPosition_horizontal_bounds
      decider symbols member
  exact congrArg GadgetSparseAssignmentTokens.assignmentTokens
    (sparseInputVertexRecordAssignment_eq_bounded _ vertex
      bounds.1 bounds.2)

end PeriodicCNFStripReduction
end LeanTrominoes
