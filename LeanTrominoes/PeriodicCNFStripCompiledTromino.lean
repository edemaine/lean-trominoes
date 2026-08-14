/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCompiledDrawing
import LeanTrominoes.GadgetStripCorrectness

/-!
# Concrete local-CNF to tromino-strip function
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- The actual target instance whose flat-encoding computation remains to be
certified polynomial-time. -/
def compiledTrominoStrip (tromino : Tromino)
    (source : PeriodicCNF Nat) : PeriodicStrip :=
  (compiledStripDrawing source).periodicStrip tromino

/-- Exact semantics of the concrete source-to-tromino-strip function. -/
theorem compiledTrominoStrip_correct
    (tromino : Tromino)
    (behavior : OrientationBehaviorCorrect tromino)
    (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      PeriodicStripTrominoTiling tromino
        (compiledTrominoStrip tromino source) := by
  exact (compiledStripDrawing_correct source).trans
    (PeriodicOrthogonalDrawing.periodicStrip_correct_of_normalized_blankBoundary
      tromino behavior (compiledStripDrawing source)
      (compiledStripDrawing_isWellFormed source)
      (compiledStripDrawing_verticesSeparated source)
      (compiledStripDrawing_hasBlankVerticalBoundary source))

end PeriodicCNFStripReduction
end LeanTrominoes
