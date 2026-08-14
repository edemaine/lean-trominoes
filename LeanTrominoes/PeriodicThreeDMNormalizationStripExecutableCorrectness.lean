/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompiler

/-! # Equality of direct and encoded-data rectangular compilers -/

namespace LeanTrominoes

namespace PeriodicThreeDM
namespace NormalizationCompiler

theorem computableCompileStrip_eq_compileStrip (input : Input) :
    computableCompileStrip input = compileStrip input := by
  apply Gadget.PeriodicOrthogonalDrawing.equivData.injective
  simp only [computableCompileStrip,
    periodicOrthogonalStripDrawingFromData, compileStripData,
    compileStrip, Gadget.PeriodicOrthogonalDrawing.equivData]

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
