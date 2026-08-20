/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestAppender

/-! # Direct affine vertex requests split by vertex kind -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Compact request for one retained monochromatic element. -/
def sparseBoundedInputElementRequestRecord
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    List GadgetSparseAffineVertexTokens.Token :=
  let position := input.drawing.vertexPosition
    input.problem.incidenceGraph (.element color atom)
  GadgetSparseAffineVertexTokens.record position.1.toNat
    (2 * input.drawing.gridSize - position.2.toNat - 1)
    (.monochromaticVertex color)

@[simp] theorem sparseBoundedInputVertexRequestRecord_element
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) (atom : Nat) :
    sparseBoundedInputVertexRequestRecord input (.element color atom) =
      sparseBoundedInputElementRequestRecord input color atom := by
  rfl

/-- Compact vertex requests split into the triple prefix and retained-element
suffix of the contracted graph. -/
theorem sparseBoundedInputVertexRequests_eq_triples_elements
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedGraph.vertices.flatMap
        (sparseBoundedInputVertexRequestRecord input) =
      input.problem.tripleVertices.flatMap
          (sparseBoundedInputVertexRequestRecord input) ++
        input.problem.contractedElementVertices.flatMap
          (sparseBoundedInputVertexRequestRecord input) := by
  simp [PeriodicThreeDM.contractedGraph]

/-- The compact retained-element suffix follows stable red, green, blue
order. -/
theorem sparseBoundedInputElementRequests_eq_colors
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    input.problem.contractedElementVertices.flatMap
        (sparseBoundedInputVertexRequestRecord input) =
      (input.problem.contractedElementVerticesForColor .red).flatMap
          (sparseBoundedInputVertexRequestRecord input) ++
        ((input.problem.contractedElementVerticesForColor .green).flatMap
          (sparseBoundedInputVertexRequestRecord input) ++
        (input.problem.contractedElementVerticesForColor .blue).flatMap
          (sparseBoundedInputVertexRequestRecord input)) := by
  simp [PeriodicThreeDM.contractedElementVertices,
    PeriodicThreeDM.incidenceColors]

/-- One constant-color block is indexed by exactly the atoms of degree three. -/
theorem sparseBoundedInputElementRequestsForColor_eq_atoms
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) :
    (input.problem.contractedElementVerticesForColor color).flatMap
        (sparseBoundedInputVertexRequestRecord input) =
      ((List.range (input.problem.elementCount color)).filter fun atom =>
          input.problem.degree color atom = 3).flatMap
        (sparseBoundedInputElementRequestRecord input color) := by
  unfold PeriodicThreeDM.contractedElementVerticesForColor
  rw [List.flatMap_map]
  rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineVertexRequestSplitStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct compact request stream is a triple block followed by three
constant-color, degree-three element blocks. -/
theorem directSparseComputedAffineVertexRequestsOfSymbols_eq_vertexKinds
    (symbols : List encoding.Γ) :
    directSparseComputedAffineVertexRequestsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.tripleVertices.flatMap
          (sparseBoundedInputVertexRequestRecord input) ++
        (((List.range (input.problem.elementCount .red)).filter fun atom =>
            input.problem.degree .red atom = 3).flatMap
            (sparseBoundedInputElementRequestRecord input .red) ++
        (((List.range (input.problem.elementCount .green)).filter fun atom =>
            input.problem.degree .green atom = 3).flatMap
            (sparseBoundedInputElementRequestRecord input .green) ++
        ((List.range (input.problem.elementCount .blue)).filter fun atom =>
            input.problem.degree .blue atom = 3).flatMap
            (sparseBoundedInputElementRequestRecord input .blue))) := by
  unfold directSparseComputedAffineVertexRequestsOfSymbols
  dsimp only
  rw [sparseBoundedInputVertexRequests_eq_triples_elements,
    sparseBoundedInputElementRequests_eq_colors,
    sparseBoundedInputElementRequestsForColor_eq_atoms,
    sparseBoundedInputElementRequestsForColor_eq_atoms,
    sparseBoundedInputElementRequestsForColor_eq_atoms]

end PeriodicCNFStripReduction
end LeanTrominoes
