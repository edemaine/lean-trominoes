/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripNormalizedDrawing
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompilerCorrectness

/-!
# Concrete local-CNF endpoint through the data-only strip compiler
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- Proof-free rectangular drawing compiler applied to the concrete retained
3DM problem-and-drawing data. -/
def compiledStripDrawing (source : PeriodicCNF Nat) :
    PeriodicOrthogonalDrawing :=
  PeriodicThreeDM.NormalizationCompiler.compileStrip
    (normalizationInput source)

/-- The runtime compiler produces exactly the semantically verified strip
drawing. -/
theorem compiledStripDrawing_eq_stripDrawing (source : PeriodicCNF Nat) :
    compiledStripDrawing source = stripDrawing source := by
  unfold compiledStripDrawing normalizationInput stripDrawing
  exact
    PeriodicThreeDM.NormalizationCompiler.compileStrip_inputOfPresentation
      (presentation source).toPlanarPresentation

theorem compiledStripDrawing_isWellFormed (source : PeriodicCNF Nat) :
    (compiledStripDrawing source).IsWellFormed := by
  rw [compiledStripDrawing_eq_stripDrawing]
  exact stripDrawing_isWellFormed source

theorem compiledStripDrawing_verticesSeparated (source : PeriodicCNF Nat) :
    (compiledStripDrawing source).VerticesSeparated := by
  rw [compiledStripDrawing_eq_stripDrawing]
  exact stripDrawing_verticesSeparated source

theorem compiledStripDrawing_hasBlankVerticalBoundary
    (source : PeriodicCNF Nat) :
    (compiledStripDrawing source).HasBlankVerticalBoundary := by
  rw [compiledStripDrawing_eq_stripDrawing]
  exact stripDrawing_hasBlankVerticalBoundary source

theorem compiledStripDrawing_correct (source : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT source ↔
      (compiledStripDrawing source).HasOrientation := by
  rw [compiledStripDrawing_eq_stripDrawing]
  exact stripDrawing_correct source

end PeriodicCNFStripReduction
end LeanTrominoes
