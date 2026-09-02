/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexCompiler

/-! # Semantics of grouped final parent clause indices -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The clause-major compiler is exactly the actual-final-clause boundary
indexer on the complete descriptor stream. -/
theorem directSourceFinalOccurrenceParentIndices_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceParentIndices decider symbols =
      HorizontalRoutedRouteHeaderFinalClauseParentIndex.parentIndices
        (directSourceFinalClauseDescriptors decider symbols) := by
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
