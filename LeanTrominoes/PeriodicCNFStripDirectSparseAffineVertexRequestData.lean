/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineVertexTokens
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexRecordDirectBounds

/-! # Compact affine requests for direct sparse vertex records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Compact data for one direct vertex record.  Its two unary fields contain
the original horizontal coordinate and the reflected vertical complement;
the fixed affine expander supplies scale 1728 and both offsets. -/
def sparseBoundedInputVertexRequestRecord
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex) :
    List GadgetSparseAffineVertexTokens.Token :=
  let position :=
    input.drawing.vertexPosition input.problem.incidenceGraph vertex
  GadgetSparseAffineVertexTokens.record position.1.toNat
    (2 * input.drawing.gridSize - position.2.toNat - 1)
    (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType input vertex)

/-- The affine interpretation of a bounded compact request is exactly the
modulus-free normalized vertex assignment. -/
theorem sparseBoundedInputVertexRequestAssignment_eq
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex)
    (horizontalNonnegative :
      0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).1)
    (horizontalLt :
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).1 <
        (input.drawing.gridSize : Int))
    (verticalNonnegative :
      0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).2)
    (verticalLt :
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).2 <
        (input.drawing.gridSize : Int)) :
    let position :=
      input.drawing.vertexPosition input.problem.incidenceGraph vertex
    GadgetSparseAffineVertexTokens.assignment position.1.toNat
        (2 * input.drawing.gridSize - position.2.toNat - 1)
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input vertex) =
      sparseBoundedInputVertexRecordAssignment input vertex := by
  rcases positionEq :
      input.drawing.vertexPosition input.problem.incidenceGraph vertex with
    ⟨horizontal, vertical⟩
  have horizontalNonnegative' : 0 ≤ horizontal := by
    simpa [positionEq] using horizontalNonnegative
  have verticalNonnegative' : 0 ≤ vertical := by
    simpa [positionEq] using verticalNonnegative
  have verticalLt' : vertical < (input.drawing.gridSize : Int) := by
    simpa [positionEq] using verticalLt
  have verticalToNatLt :
      vertical.toNat < input.drawing.gridSize := by
    rw [← Int.ofNat_lt,
      Int.toNat_of_nonneg verticalNonnegative']
    exact verticalLt'
  have verticalToNatLeDouble :
      vertical.toNat ≤ 2 * input.drawing.gridSize := by
    omega
  have oneLeComplement :
      1 ≤ 2 * input.drawing.gridSize - vertical.toNat := by
    omega
  have complementCast :
      ((2 * input.drawing.gridSize - vertical.toNat - 1 : Nat) : Int) =
        2 * (input.drawing.gridSize : Int) - vertical - 1 := by
    rw [Nat.cast_sub oneLeComplement,
      Nat.cast_sub verticalToNatLeDouble]
    push_cast
    rw [Int.toNat_of_nonneg verticalNonnegative']
  unfold GadgetSparseAffineVertexTokens.assignment
    sparseBoundedInputVertexRecordAssignment
  rw [positionEq]
  apply Prod.ext
  · apply Prod.ext
    · push_cast
      rw [Int.toNat_of_nonneg horizontalNonnegative']
    · push_cast
      rw [complementCast]
      ring
  · rfl

/-- Fixed affine expansion recovers one exact canonical direct vertex
record. -/
theorem expand_sparseBoundedInputVertexRequestRecord
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (vertex : PeriodicThreeDMVertex)
    (horizontalNonnegative :
      0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).1)
    (horizontalLt :
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).1 <
        (input.drawing.gridSize : Int))
    (verticalNonnegative :
      0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).2)
    (verticalLt :
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).2 <
        (input.drawing.gridSize : Int)) :
    GadgetSparseAffineVertexTokens.expand
        (sparseBoundedInputVertexRequestRecord input vertex) =
      GadgetSparseAssignmentTokens.assignmentTokens
        (sparseBoundedInputVertexRecordAssignment input vertex) := by
  unfold sparseBoundedInputVertexRequestRecord
  rw [GadgetSparseAffineVertexTokens.expand_record]
  exact congrArg GadgetSparseAssignmentTokens.assignmentTokens
    (sparseBoundedInputVertexRequestAssignment_eq input vertex
      horizontalNonnegative horizontalLt verticalNonnegative verticalLt)

/-- Compact request stream for every direct contracted vertex. -/
def directSparseComputedAffineVertexRequestsOfSymbols
    {Input : Type}
    {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  input.problem.contractedGraph.vertices.flatMap
    (sparseBoundedInputVertexRequestRecord input)

theorem affineExpand_flatMap {Value : Type}
    (values : List Value)
    (request : Value → List GadgetSparseAffineVertexTokens.Token) :
    GadgetSparseAffineVertexTokens.expand (values.flatMap request) =
      values.flatMap fun value =>
        GadgetSparseAffineVertexTokens.expand (request value) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.flatMap_cons, GadgetSparseAffineVertexTokens.expand_append,
        List.flatMap_cons, induction]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineVertexRequestDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Expanding all compact direct requests gives the exact previously verified
canonical vertex-record prefix. -/
theorem expand_directSparseComputedAffineVertexRequestsOfSymbols
    (symbols : List encoding.Γ) :
    GadgetSparseAffineVertexTokens.expand
        (directSparseComputedAffineVertexRequestsOfSymbols decider symbols) =
      directSparseComputedVertexRecordsOfSymbols decider symbols := by
  rw [directSparseComputedVertexRecordsOfSymbols_eq_boundedBlocks]
  unfold directSparseComputedAffineVertexRequestsOfSymbols
  dsimp only
  rw [affineExpand_flatMap]
  apply List.flatMap_congr
  intro vertex member
  have bounds :=
    directSparseComputedInput_vertexPosition_bounds decider symbols member
  exact expand_sparseBoundedInputVertexRequestRecord _ vertex
    bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2

end PeriodicCNFStripReduction
end LeanTrominoes
