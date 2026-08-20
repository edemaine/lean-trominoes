/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedRecordBlocks

/-! # Affine vertex blocks of direct sparse assignment records -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Expanding the three compiler normalization rounds gives scale `12³` and
translation `3 · (12² + 12 + 1) = 471`. -/
theorem normalizationCompiler_finalNormalizationPosition_eq_scaleCube
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationPosition
        input vertex =
      Cell.add (Cell.scale 1728
        (PeriodicThreeDM.NormalizationCompiler.normalizationPosition0
          input vertex)) (471, 471) := by
  rcases positionEq :
      PeriodicThreeDM.NormalizationCompiler.normalizationPosition0
        input vertex with ⟨horizontal, vertical⟩
  simp only [
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationPosition,
    PeriodicThreeDM.NormalizationCompiler.normalizationPosition2,
    PeriodicThreeDM.NormalizationCompiler.normalizationPosition1,
    PeriodicThreeDM.normalizeVertexPosition,
    PeriodicThreeDM.vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add,
    positionEq, Prod.mk.injEq]
  constructor <;> ring

/-- The data-only compiler's final period is exactly `1728` times the input
drawing period. -/
@[simp] theorem normalizationCompiler_finalNormalizationPeriod_eq_scaleCube
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod input =
      1728 * input.drawing.gridSize := by
  simp [PeriodicThreeDM.NormalizationCompiler.finalNormalizationPeriod,
    PeriodicThreeDM.vertexNormalizationScaleNat,
    PeriodicThreeDM.NormalizationCompiler.contractedDrawing,
    PeriodicGridDrawing.gridSize]

/-- Shallow affine data for one final strip vertex assignment. -/
def sparseVertexRecordAssignment
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    Cell × OrthogonalCellType :=
  let position :=
    PeriodicThreeDM.NormalizationCompiler.normalizationPosition0 input vertex
  let period := 1728 * input.drawing.gridSize
  (((1728 * position.1 + 471) % period,
      2 * (period : Int) - (1728 * position.2 + 471)),
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType input vertex)

/-- One vertex record depends only on the original contracted position, the
input grid size, and the finite final vertex type. -/
theorem sparseVertexRecordBlock_eq_affine
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    sparseVertexRecordBlock input vertex =
      GadgetSparseAssignmentTokens.assignmentTokens
        (sparseVertexRecordAssignment input vertex) := by
  unfold sparseVertexRecordBlock sparseVertexRecordAssignment
  rw [normalizationCompiler_finalNormalizationPosition_eq_scaleCube,
    normalizationCompiler_finalNormalizationPeriod_eq_scaleCube]
  rcases positionEq :
      PeriodicThreeDM.NormalizationCompiler.normalizationPosition0
        input vertex with ⟨horizontal, vertical⟩
  simp [PeriodicThreeDM.stripRasterLocation, Cell.scale, Cell.add]

theorem sparseVertexRecordBlocks_eq_affineBlocks
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertices : List PeriodicThreeDMVertex) :
    vertices.flatMap (sparseVertexRecordBlock input) =
      vertices.flatMap fun vertex =>
        GadgetSparseAssignmentTokens.assignmentTokens
          (sparseVertexRecordAssignment input vertex) := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices induction =>
      simp only [List.flatMap_cons]
      rw [sparseVertexRecordBlock_eq_affine, induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseVertexRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct vertex-record prefix is a flat map of shallow affine record
blocks over the contracted vertices. -/
theorem directSparseComputedVertexRecordsOfSymbols_eq_affineBlocks
    (symbols : List encoding.Γ) :
    directSparseComputedVertexRecordsOfSymbols decider symbols =
      let input := directSparseComputedNormalizationInputOfSymbols
        decider symbols
      input.problem.contractedGraph.vertices.flatMap fun vertex =>
        GadgetSparseAssignmentTokens.assignmentTokens
          (sparseVertexRecordAssignment input vertex) := by
  rw [directSparseComputedVertexRecordsOfSymbols_eq_blocks]
  exact sparseVertexRecordBlocks_eq_affineBlocks _ _

end PeriodicCNFStripReduction
end LeanTrominoes
