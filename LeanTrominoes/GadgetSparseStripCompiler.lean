/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseStripData
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompiler

/-! # Data-only sparse normalization-strip compiler -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

open Gadget

/-- Build the assignment-order sparse gadget strip from proof-free
normalization input data. -/
def compileSparseStrip (tromino : Tromino) (input : Input) : PeriodicStrip where
  width := 6 * finalStripHeight input
  period := 6 * finalNormalizationPeriod input
  motif := sparseExpandedMotif tromino (finalStripCellAssignments input)

@[simp] theorem compileSparseStrip_motif
    (tromino : Tromino) (input : Input) :
    (compileSparseStrip tromino input).motif =
      sparseExpandedMotif tromino (finalStripCellAssignments input) :=
  rfl

/-- Data-only and proof-backed strip assignment lists agree exactly. -/
@[simp] theorem finalStripCellAssignments_inputOfPresentation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    finalStripCellAssignments (inputOfPresentation presentation) =
      presentation.finalStripCellAssignments := by
  set_option maxRecDepth 100000 in
    rfl

/-- The data-only sparse compiler is definitionally the proof-backed sparse
strip substitution. -/
theorem compileSparseStrip_inputOfPresentation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (tromino : Tromino) :
    compileSparseStrip tromino
        (inputOfPresentation presentation.toPlanarPresentation) =
      presentation.sparsePeriodicStrip tromino := by
  set_option maxRecDepth 100000 in
    rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
