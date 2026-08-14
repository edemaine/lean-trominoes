/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripCompiler

/-! # Correctness interface for the data-only rectangular compiler -/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- The data-only compiler is definitionally the verified presentation-level
rectangular construction. -/
theorem compileStrip_inputOfPresentation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    compileStrip (inputOfPresentation presentation) =
      presentation.stripNormalizedOrthogonalDrawing := by
  set_option maxRecDepth 100000 in
    rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
