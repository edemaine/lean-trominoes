/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitOffsets
import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRoutes

/-! # Exact offset words of magnified normalization routes -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget
open DegreeThreeVertexNormalization

/-- The normalization affine map is factor-twelve scaling followed by the
fixed template-center translation. -/
theorem map_normalizeVertexPosition_eq_translate_scalePolyline_steps
    (points : List Cell) :
    points.map normalizeVertexPosition =
      PeriodicOrthocrossing.translatePolyline center
        (scalePolyline 12 points) := by
  induction points with
  | nil => rfl
  | cons point points induction =>
      simp only [List.map_cons, scalePolyline_cons,
        PeriodicOrthocrossing.translatePolyline, induction]
      rcases point with ⟨pointX, pointY⟩
      simp [normalizeVertexPosition, vertexNormalizationScale,
        center, Cell.add, Cell.scale, Int.add_comm]

/-- Magnifying and subdividing an orthogonal route applies the fixed
twelve-copy transduction to its segment-major subdivision word. -/
theorem routeStepOffsets_magnifiedUnitRoute
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    routeStepOffsets (magnifiedUnitRoute points) =
      repeatTwelveOffsets (unitSubdivisionOffsets points) := by
  have scaledOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (scalePolyline 12 points) :=
    orthogonal.scalePolyline (factor := 12) (by omega)
  unfold magnifiedUnitRoute
  rw [map_normalizeVertexPosition_eq_translate_scalePolyline_steps]
  unfold PeriodicOrthocrossing.translatePolyline
  rw [AxisDirection.unitSubdividePolyline_map_add]
  change routeStepOffsets
      (PeriodicOrthocrossing.translatePolyline center
        (AxisDirection.unitSubdividePolyline
          (scalePolyline 12 points))) = _
  rw [routeStepOffsets_translatePolyline]
  rw [routeStepOffsets_unitSubdividePolyline _ scaledOrthogonal]
  rw [unitSubdivisionOffsets_scale_twelve]

/-- In the second and third rounds, whose old route is already unit-step,
magnification is literally the twelve-copy transduction on exact offsets. -/
theorem routeStepOffsets_magnifiedUnitRoute_of_unitSteps
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    routeStepOffsets (magnifiedUnitRoute points) =
      repeatTwelveOffsets (routeStepOffsets points) := by
  have orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points :=
    unitSteps.imp fun _ _ unit =>
      AxisDirection.isAxisAligned_of_between_isGenuine
        (AxisDirection.between_isGenuine_of_unitAxisStep unit)
  rw [routeStepOffsets_magnifiedUnitRoute points orthogonal]
  rw [unitSubdivisionOffsets_eq_routeStepOffsets points unitSteps]

end PeriodicThreeDM
end LeanTrominoes
