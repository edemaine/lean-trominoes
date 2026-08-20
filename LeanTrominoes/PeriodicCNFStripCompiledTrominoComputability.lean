/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCompiledTromino
import LeanTrominoes.PeriodicCNFStripNormalizationInputComputability
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompileComputability

/-! # Computability of the concrete CNF-to-tromino-strip compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget

/-- The exact rectangular drawing used by the semantic reduction is
computable through the proof-free normalization input. -/
theorem compiledStripDrawing_computable : Computable compiledStripDrawing := by
  unfold compiledStripDrawing
  exact
    PeriodicThreeDM.NormalizationCompiler.compileStrip_computable.comp
      normalizationInput_computable

/-- For either tromino, the complete finite target strip is computable. -/
theorem compiledTrominoStrip_computable (tromino : Tromino) :
    Computable (compiledTrominoStrip tromino) := by
  unfold compiledTrominoStrip
  exact
    (PeriodicOrthogonalDrawing.periodicStrip_computable tromino).comp
      compiledStripDrawing_computable

end PeriodicCNFStripReduction
end LeanTrominoes
