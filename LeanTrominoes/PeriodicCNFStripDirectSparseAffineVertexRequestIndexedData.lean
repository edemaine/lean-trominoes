/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexRequestElementIndexed

/-! # Complete indexed direct affine vertex-request stream -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Triple requests as a direct scan of computed positions and stable indices. -/
def directSparseComputedAffineIndexedTripleRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (horizontalThreeDMTriplePositionsComputed source).zipIdx.flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2))

/-- One monochromatic request block as a filtered direct scan of the computed
position list for its color. -/
def directSparseComputedAffineIndexedElementRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input)
    (color : WireColor) :
    List GadgetSparseAffineVertexTokens.Token :=
  ((horizontalThreeDMElementPositionsComputed source color).zipIdx.filter
      fun tagged => input.problem.degree color tagged.2 = 3).flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1 (.monochromaticVertex color)

/-- Complete lookup-free indexed request stream in contracted-vertex order. -/
def directSparseComputedAffineIndexedVertexRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  directSparseComputedAffineIndexedTripleRequests source input ++
    (directSparseComputedAffineIndexedElementRequests source input .red ++
      (directSparseComputedAffineIndexedElementRequests source input .green ++
        directSparseComputedAffineIndexedElementRequests source input .blue))

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineVertexRequestIndexedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Indexed request stream generated from raw direct-source symbols. -/
def directSparseComputedAffineIndexedVertexRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  directSparseComputedAffineIndexedVertexRequests source input

/-- The original compact direct request stream is exactly the four indexed
computed-position scans. -/
theorem directSparseComputedAffineVertexRequestsOfSymbols_eq_indexed
    (symbols : List encoding.Γ) :
    directSparseComputedAffineVertexRequestsOfSymbols decider symbols =
      directSparseComputedAffineIndexedVertexRequestsOfSymbols
        decider symbols := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  let input := directSparseComputedNormalizationInputOfSymbols
    decider symbols
  have problemEq :
      input.problem = horizontalThreeDMProblemComputed source := by
    rfl
  rw [directSparseComputedAffineVertexRequestsOfSymbols_eq_positionAt,
    directSparseComputedAffineVertexRequestsAtOfSymbols_eq_vertexKinds]
  change
    input.problem.tripleVertices.flatMap
        (directSparseComputedAffineVertexRequestRecordAt source input) ++
      (((List.range (input.problem.elementCount .red)).filter fun atom =>
          input.problem.degree .red atom = 3).flatMap
          (directSparseComputedAffineElementRequestRecordAt
            source input .red) ++
      (((List.range (input.problem.elementCount .green)).filter fun atom =>
          input.problem.degree .green atom = 3).flatMap
          (directSparseComputedAffineElementRequestRecordAt
            source input .green) ++
      ((List.range (input.problem.elementCount .blue)).filter fun atom =>
          input.problem.degree .blue atom = 3).flatMap
          (directSparseComputedAffineElementRequestRecordAt
            source input .blue))) =
      directSparseComputedAffineIndexedVertexRequests source input
  unfold directSparseComputedAffineIndexedVertexRequests
    directSparseComputedAffineIndexedTripleRequests
    directSparseComputedAffineIndexedElementRequests
  rw [directSparseComputedAffineTripleRequestsAt_eq_zipIdx
      source input problemEq,
    directSparseComputedAffineElementRequestsAtForColor_eq_zipIdx
      source input .red problemEq,
    directSparseComputedAffineElementRequestsAtForColor_eq_zipIdx
      source input .green problemEq,
    directSparseComputedAffineElementRequestsAtForColor_eq_zipIdx
      source input .blue problemEq]

end PeriodicCNFStripReduction
end LeanTrominoes
