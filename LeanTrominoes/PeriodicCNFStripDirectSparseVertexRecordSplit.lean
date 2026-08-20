/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexInputData

/-! # Triple and monochromatic direct sparse vertex-record streams -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- One record block from the original input drawing's vertex lookup. -/
def sparseInputVertexRecordBlock
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentTokens
    (sparseInputVertexRecordAssignment input vertex)

/-- Explicit assignment data for one retained monochromatic element. -/
def sparseInputElementRecordAssignment
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    Cell × OrthogonalCellType :=
  let position := input.drawing.vertexPosition
    input.problem.incidenceGraph (.element color atom)
  let period := 1728 * input.drawing.gridSize
  (((1728 * position.1 + 471) % period,
      2 * (period : Int) - (1728 * position.2 + 471)),
    .monochromaticVertex color)

/-- One retained element block has its color as a constant cell-type tag. -/
def sparseInputElementRecordBlock
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentTokens
    (sparseInputElementRecordAssignment input color atom)

@[simp] theorem sparseInputVertexRecordBlock_element
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    sparseInputVertexRecordBlock input (.element color atom) =
      sparseInputElementRecordBlock input color atom := by
  rfl

/-- Contracted vertex records split exactly into their triple prefix and
retained-element suffix. -/
theorem sparseInputVertexRecordBlocks_eq_triples_elements
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedGraph.vertices.flatMap
        (sparseInputVertexRecordBlock input) =
      input.problem.tripleVertices.flatMap
          (sparseInputVertexRecordBlock input) ++
        input.problem.contractedElementVertices.flatMap
          (sparseInputVertexRecordBlock input) := by
  simp [PeriodicThreeDM.contractedGraph]

/-- The retained-element suffix is grouped in stable red, green, blue order. -/
theorem sparseInputElementRecordBlocks_eq_colors
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedElementVertices.flatMap
        (sparseInputVertexRecordBlock input) =
      (input.problem.contractedElementVerticesForColor .red).flatMap
          (sparseInputVertexRecordBlock input) ++
        ((input.problem.contractedElementVerticesForColor .green).flatMap
          (sparseInputVertexRecordBlock input) ++
        (input.problem.contractedElementVerticesForColor .blue).flatMap
          (sparseInputVertexRecordBlock input)) := by
  simp [PeriodicThreeDM.contractedElementVertices,
    PeriodicThreeDM.incidenceColors]

/-- A color block is indexed only by the degree-three element numbers of that
color, with a constant monochromatic cell type. -/
theorem sparseInputElementRecordBlocksForColor_eq_atoms
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) :
    (input.problem.contractedElementVerticesForColor color).flatMap
        (sparseInputVertexRecordBlock input) =
      ((List.range (input.problem.elementCount color)).filter fun atom =>
          input.problem.degree color atom = 3).flatMap
        (sparseInputElementRecordBlock input color) := by
  unfold PeriodicThreeDM.contractedElementVerticesForColor
  rw [List.flatMap_map]
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseVertexRecordSplitStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct vertex-record prefix is a triple block followed by three
constant-color element blocks. -/
theorem directSparseComputedVertexRecordsOfSymbols_eq_vertexKinds
    (symbols : List encoding.Γ) :
    directSparseComputedVertexRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.tripleVertices.flatMap
          (sparseInputVertexRecordBlock input) ++
        (((List.range (input.problem.elementCount .red)).filter fun atom =>
            input.problem.degree .red atom = 3).flatMap
            (sparseInputElementRecordBlock input .red) ++
        (((List.range (input.problem.elementCount .green)).filter fun atom =>
            input.problem.degree .green atom = 3).flatMap
            (sparseInputElementRecordBlock input .green) ++
        ((List.range (input.problem.elementCount .blue)).filter fun atom =>
            input.problem.degree .blue atom = 3).flatMap
            (sparseInputElementRecordBlock input .blue))) := by
  rw [directSparseComputedVertexRecordsOfSymbols_eq_inputBlocks]
  change
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    input.problem.contractedGraph.vertices.flatMap
        (sparseInputVertexRecordBlock input) = _
  dsimp only
  rw [sparseInputVertexRecordBlocks_eq_triples_elements,
    sparseInputElementRecordBlocks_eq_colors,
    sparseInputElementRecordBlocksForColor_eq_atoms,
    sparseInputElementRecordBlocksForColor_eq_atoms,
    sparseInputElementRecordBlocksForColor_eq_atoms]

end PeriodicCNFStripReduction
end LeanTrominoes
