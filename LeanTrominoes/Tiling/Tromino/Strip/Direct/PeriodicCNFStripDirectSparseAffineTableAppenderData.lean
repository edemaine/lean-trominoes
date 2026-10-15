/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectSparseAffineTripleTableScan
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectSparseAffineClauseElementTableScan
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectSparseAffineVertexIndexedAppenderData
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed

/-! # Table-driven source-symbol contracts for affine vertex appenders -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Table-driven variable-triple requests generated from raw source symbols. -/
def directSparseComputedAffineTableVariableTripleRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.ProgramSource.formulaOfSymbols
    decider symbols
  directSparseComputedAffineTypedTableVariableTripleRequests source

/-- Table-driven clause-triple requests generated from raw source symbols. -/
def directSparseComputedAffineTableClauseTripleRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.ProgramSource.formulaOfSymbols
    decider symbols
  directSparseComputedAffineTableClauseTripleRequests source

/-- Complete table-driven triple requests in canonical variable-prefix,
clause-suffix order. -/
def directSparseComputedAffineTableTripleRequestsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  directSparseComputedAffineTableVariableTripleRequestsOfSymbols
      decider symbols ++
    directSparseComputedAffineTableClauseTripleRequestsOfSymbols
      decider symbols

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
    directSparseComputedAffineTableVariableTripleRequestsOfSymbols
    directSparseComputedAffineTableClauseTripleRequestsOfSymbols
  exact directSparseComputedAffineIndexedTripleRequests_eq_cellTables
    (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)

/-- Table-driven retained clause-element requests of one color. -/
def directSparseComputedAffineTableElementRequestsOfSymbols
    (color : WireColor) (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  let source := PeriodicCNF.ProgramSource.formulaOfSymbols
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
  let source := PeriodicCNF.ProgramSource.formulaOfSymbols
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
