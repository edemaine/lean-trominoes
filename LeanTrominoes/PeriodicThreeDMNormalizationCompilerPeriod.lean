/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler

/-!
# Period projection for normalization compiler inputs
-/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

@[simp] theorem finalNormalizationPeriod_inputOfPresentation
    (problem : PeriodicThreeDM)
    (presentation : problem.PlanarPresentation) :
    finalNormalizationPeriod (inputOfPresentation presentation) =
      vertexNormalizationScaleNat ^ 3 * presentation.drawing.gridSize := by
  rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
