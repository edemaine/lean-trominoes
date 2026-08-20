/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseStripCompiler
import LeanTrominoes.GadgetSparseStripSemantics
import LeanTrominoes.PeriodicCNFStripCompiledTromino
import LeanTrominoes.PeriodicCNFStripHorizontalProblem

/-! # Sparse local-CNF to tromino-strip reduction -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- The same verified strip reduction with its gadget motif listed directly
from nonblank normalization assignments rather than a complete raster scan. -/
def sparseCompiledTrominoStrip (tromino : Tromino)
    (source : PeriodicCNF Nat) : PeriodicStrip :=
  PeriodicThreeDM.NormalizationCompiler.compileSparseStrip tromino
    (normalizationInput source)

/-- Sparse assignment order preserves the exact local-CNF tiling semantics. -/
theorem sparseCompiledTrominoStrip_correct
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino)
    (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      PeriodicStripTrominoTiling tromino
        (sparseCompiledTrominoStrip tromino source) := by
  unfold sparseCompiledTrominoStrip normalizationInput
  rw [PeriodicThreeDM.NormalizationCompiler.compileSparseStrip_inputOfPresentation]
  have sparseDense :=
    (presentation source).sparsePeriodicStrip_tiling_iff
      (presentation source).problemWellFormed
      (problem_degreeTwoOrThree source)
      (problem_isOneDimensional source)
      (presentation_routePointsInExpandedVerticalBand source)
      (presentation_separated source)
      (presentation_routesSimple source)
      tromino
  have denseEquality :
      ((presentation source).toPlanarPresentation
          |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino) =
        compiledTrominoStrip tromino source := by
    unfold compiledTrominoStrip
    rw [compiledStripDrawing_eq_stripDrawing]
    rfl
  rw [denseEquality] at sparseDense
  exact (compiledTrominoStrip_correct tromino behavior source).trans
    sparseDense.symm

end PeriodicCNFStripReduction
end LeanTrominoes
