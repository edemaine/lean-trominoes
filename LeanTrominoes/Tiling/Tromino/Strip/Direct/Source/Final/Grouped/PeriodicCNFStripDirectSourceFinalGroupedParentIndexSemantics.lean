/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Grouped.PeriodicCNFStripDirectSourceFinalGroupedParentIndexCompiler

/-! # Semantics of grouped final parent clause indices -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- The clause-major compiler is exactly the actual-final-clause boundary
specification: each clause ordinal is repeated over precisely that clause's
occurrence-frame block. -/
theorem directSourceFinalOccurrenceParentIndices_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceParentIndices decider symbols =
      FiniteBlockIndices.expected List.length
        (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
          (directSourceFinalClauseDescriptors decider symbols)) := by
  unfold directSourceFinalOccurrenceParentIndices
  exact
    HorizontalRoutedRouteHeaderFinalClauseParentIndex.parentIndices_eq_expected
      _

end LeanTrominoes.PeriodicCNFStripReduction
