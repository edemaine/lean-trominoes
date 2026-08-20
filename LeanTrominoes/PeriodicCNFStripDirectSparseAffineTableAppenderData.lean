/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTripleTableScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineClauseElementTableScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVertexIndexedAppenderData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed

/-! # Table-driven source-symbol contracts for affine vertex appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineTableAppenderDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Table-driven triple requests generated from raw source symbols. -/
def directSparseComputedAffineTableTripleRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  directSparseComputedAffineTypedTableVariableTripleRequests source ++
    directSparseComputedAffineTableClauseTripleRequests source

/-- The table-driven triple word is exactly the indexed triple-appender
target. -/
theorem directSparseComputedAffineIndexedTripleRequestsOfSymbols_eq_table
    (symbols : List encoding.Γ) :
    directSparseComputedAffineIndexedTripleRequestsOfSymbols
        decider symbols =
      directSparseComputedAffineTableTripleRequestsOfSymbols
        decider symbols := by
  unfold directSparseComputedAffineIndexedTripleRequestsOfSymbols
    directSparseComputedAffineTableTripleRequestsOfSymbols
  exact directSparseComputedAffineIndexedTripleRequests_eq_cellTables
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- Table-driven retained clause-element requests of one color. -/
def directSparseComputedAffineTableElementRequestsOfSymbols
    (color : WireColor) (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  directSparseComputedAffineTableClauseElementRequests
    source (horizontalNormalizationInputComputed source) color

/-- Every indexed color block is exactly its uniform retained-clause table
scan. -/
theorem directSparseComputedAffineIndexedElementRequestsOfSymbols_eq_table
    (color : WireColor) (symbols : List encoding.Γ) :
    directSparseComputedAffineIndexedElementRequestsOfSymbols
        decider color symbols =
      directSparseComputedAffineTableElementRequestsOfSymbols
        decider color symbols := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  have problemEq :
      (horizontalNormalizationInputComputed source).problem =
        horizontalThreeDMPositionProblemComputed source := by
    rw [horizontalNormalizationInputComputed_problem,
      ← horizontalThreeDMPositionProblemComputed_eq]
  cases color with
  | red =>
      exact directSparseComputedAffineIndexedRedRequests_eq_table
        source (horizontalNormalizationInputComputed source) problemEq
  | green =>
      exact directSparseComputedAffineIndexedGreenRequests_eq_table
        source (horizontalNormalizationInputComputed source) problemEq
  | blue =>
      exact directSparseComputedAffineIndexedBlueRequests_eq_table
        source (horizontalNormalizationInputComputed source) problemEq

end PeriodicCNFStripReduction
end LeanTrominoes
