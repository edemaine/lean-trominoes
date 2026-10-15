/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.FiniteThreeDMNormalization

/-! # Finite normalized drawing dimensions without unfolding its cell data -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget Gadget.PeriodicOrthogonalDrawing

private theorem period_eq {problem : PeriodicThreeDM} (p : problem.PlanarPresentation) :
    p.finalNormalizationPeriod=vertexNormalizationScaleNat^3*p.drawing.gridSize := rfl

theorem ContinuousPlanarPresentation.finiteNormalizedDrawing_periods {problem : PeriodicThreeDM}
    (p : problem.ContinuousPlanarPresentation) (zero : problem.ZeroOffsets)
    (bounds : p.drawing.SegmentEndpointsInExpandedSquare) :
    (p.finiteNormalizedDrawing zero bounds).horizontalPeriod=
      vertexNormalizationScaleNat^3*p.drawing.finitePad.gridSize ∧
    (p.finiteNormalizedDrawing zero bounds).verticalPeriod=
      3*(vertexNormalizationScaleNat^3*p.drawing.finitePad.gridSize)+1 := by
  have result := (p.finitePad zero bounds).toPlanarPresentation.stripNormalizedOrthogonalDrawing_periods
  simpa only [ContinuousPlanarPresentation.finiteNormalizedDrawing,moveSeam,horizontalPeriod,verticalPeriod,
    PlanarPresentation.finalStripHeight,period_eq,ContinuousPlanarPresentation.finitePad] using result
end LeanTrominoes.PeriodicThreeDM
