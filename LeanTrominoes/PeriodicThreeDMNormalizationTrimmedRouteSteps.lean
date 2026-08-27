/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepSlicing
import LeanTrominoes.PeriodicThreeDMNormalizationMagnifiedRouteSteps

/-! # Exact offset words of trimmed magnified routes -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Endpoint trimming after magnification is a fixed slice of the repeated
segment-major offset word. -/
theorem routeStepOffsets_trimmedMagnifiedRoute
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    routeStepOffsets (trimmedMagnifiedRoute points) =
      trimThreeOffsets
        (repeatTwelveOffsets (unitSubdivisionOffsets points)) := by
  unfold trimmedMagnifiedRoute
  rw [routeStepOffsets_trim_three]
  rw [routeStepOffsets_magnifiedUnitRoute points orthogonal]

/-- On an already unit-step old route, the trimmed middle corridor is a
fixed slice of the twelve-copy expansion of its exact offsets. -/
theorem routeStepOffsets_trimmedMagnifiedRoute_of_unitSteps
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    routeStepOffsets (trimmedMagnifiedRoute points) =
      trimThreeOffsets
        (repeatTwelveOffsets (routeStepOffsets points)) := by
  have orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points :=
    unitSteps.imp fun _ _ unit =>
      AxisDirection.isAxisAligned_of_between_isGenuine
        (AxisDirection.between_isGenuine_of_unitAxisStep unit)
  rw [routeStepOffsets_trimmedMagnifiedRoute points orthogonal]
  rw [unitSubdivisionOffsets_eq_routeStepOffsets points unitSteps]

end PeriodicThreeDM
end LeanTrominoes
