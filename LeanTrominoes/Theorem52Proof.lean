/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVertexRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler
import LeanTrominoes.Theorem52DirectSparseClosure

/-! # Unconditional proof of Theorem 5.2 -/

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Both concrete geometry appenders are available uniformly for every encoded
source language and its polynomial-space decider. -/
theorem directSparseSplitRecordAppenders : DirectSparseSplitRecordAppenders := by
  intro Input encoding language decider
  exact ⟨⟨directSparseVertexRecordAppender decider⟩, ⟨directSparseRouteRecordAppender decider⟩⟩

end LeanTrominoes.PeriodicCNFStripReduction

namespace LeanTrominoes.Theorem52

/-- For each tromino, periodic plane tiling is co-r.e.-complete and periodic
strip tiling under the flat encoding is PSPACE-complete. -/
theorem proved : statement :=
  PeriodicCNFStripReduction.theorem52_statement_of_directSparseSplitRecordAppenders
    PeriodicCNFStripReduction.directSparseSplitRecordAppenders

/-- The full strip assertion, including the polynomial-time hardness reduction. -/
theorem stripProved : stripStatement := proved.2

end LeanTrominoes.Theorem52
