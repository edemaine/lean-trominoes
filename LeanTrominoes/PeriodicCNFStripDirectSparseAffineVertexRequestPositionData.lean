/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestSplit
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed

/-! # Direct affine requests from computed pointwise positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- One compact request using the explicit computed pointwise position table
instead of a drawing-table lookup. -/
def directSparseComputedAffineVertexRequestRecordAt
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    List GadgetSparseAffineVertexTokens.Token :=
  let position := horizontalThreeDMVertexPositionAtComputed source vertex
  GadgetSparseAffineVertexTokens.record position.1.toNat
    (2 * input.drawing.gridSize - position.2.toNat - 1)
    (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType input vertex)

/-- On a retained vertex, the original lookup-based request is exactly the
pointwise computed-position request. -/
theorem sparseBoundedInputVertexRequestRecord_eq_computedPositionAt
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (inputEq : horizontalNormalizationInputComputed source =
      input)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ input.problem.contractedGraph.vertices) :
    sparseBoundedInputVertexRequestRecord input vertex =
      directSparseComputedAffineVertexRequestRecordAt source input vertex := by
  have problemEq :
      input.problem = horizontalThreeDMProblemComputed source := by
    rw [← inputEq]
    rfl
  have drawingEq :
      input.drawing = horizontalThreeDMDrawingComputed source := by
    rw [← inputEq]
    rfl
  have incidenceMember : vertex ∈
      (horizontalThreeDMProblemComputed source).incidenceGraph.vertices := by
    rw [← problemEq]
    exact PeriodicThreeDM.contractedGraph_vertex_mem_incidenceGraph
      input.problem member
  unfold sparseBoundedInputVertexRequestRecord
    directSparseComputedAffineVertexRequestRecordAt
  rw [drawingEq, problemEq,
    horizontalThreeDMDrawingComputed_vertexPosition_eq_positionAt
      source incidenceMember]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineVertexRequestPositionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct compact requests stated as a traversal of the pointwise computed
position table. -/
def directSparseComputedAffineVertexRequestsAtOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  input.problem.contractedGraph.vertices.flatMap
    (directSparseComputedAffineVertexRequestRecordAt source input)

/-- The lookup-free pointwise stream is exactly the compact direct request
stream used by the retained-input appender boundary. -/
theorem directSparseComputedAffineVertexRequestsOfSymbols_eq_positionAt
    (symbols : List encoding.Γ) :
    directSparseComputedAffineVertexRequestsOfSymbols decider symbols =
      directSparseComputedAffineVertexRequestsAtOfSymbols decider symbols := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  change input.problem.contractedGraph.vertices.flatMap
      (sparseBoundedInputVertexRequestRecord input) =
    input.problem.contractedGraph.vertices.flatMap
      (directSparseComputedAffineVertexRequestRecordAt source input)
  apply List.flatMap_congr
  intro vertex member
  exact sparseBoundedInputVertexRequestRecord_eq_computedPositionAt
    source input (by rfl) member

end PeriodicCNFStripReduction
end LeanTrominoes
