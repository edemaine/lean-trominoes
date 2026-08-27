/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRouteStepTransform

/-! # One-round normalization over the finite direction alphabet

The coordinate-offset transform for a normalization round can be represented
over the five-symbol `AxisDirection` alphabet whenever its input routes are
unit routes.  This is the semantic interface needed by a finite-alphabet
Turing-machine implementation.
-/

namespace LeanTrominoes
namespace Gadget

/-- Fixed block transduction replacing every direction by twelve copies. -/
def repeatTwelveDirections
    (directions : List AxisDirection) : List AxisDirection :=
  directions.flatMap fun direction => List.replicate 12 direction

/-- Taking unit steps commutes with the fixed twelve-copy expansion. -/
@[simp]
theorem map_step_repeatTwelveDirections
    (directions : List AxisDirection) :
    (repeatTwelveDirections directions).map AxisDirection.step =
      repeatTwelveOffsets (directions.map AxisDirection.step) := by
  simp only [repeatTwelveDirections, repeatTwelveOffsets,
    List.map_flatMap, List.flatMap_map, List.map_replicate]

/-- Direction-level form of removing three steps from both ends. -/
def trimThreeDirections
    (directions : List AxisDirection) : List AxisDirection :=
  (directions.drop 3).take (directions.length - 6)

/-- Taking unit steps commutes with endpoint trimming. -/
@[simp]
theorem map_step_trimThreeDirections
    (directions : List AxisDirection) :
    (trimThreeDirections directions).map AxisDirection.step =
      trimThreeOffsets (directions.map AxisDirection.step) := by
  simp [trimThreeDirections, trimThreeOffsets]

/-- Symmetric, total-list form of the unit-route direction/offset theorem. -/
theorem map_routeStepDirections_step_eq_routeStepOffsets
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    (routeStepDirections points).map AxisDirection.step =
      routeStepOffsets points := by
  cases points with
  | nil => simp [routeStepDirections, routeStepOffsets]
  | cons first rest =>
      exact (routeStepOffsets_eq_map_routeStepDirections
        first rest unitSteps).symm

end Gadget

namespace PeriodicThreeDM

open Gadget

/-- One normalization round expressed entirely as a finite direction word. -/
def normalizationDirectionWord
    (sourceTemplate targetTemplate : List Cell)
    (oldDirections : List AxisDirection) : List AxisDirection :=
  routeStepDirections sourceTemplate ++
    (trimThreeDirections (repeatTwelveDirections oldDirections) ++
      routeStepDirections targetTemplate.reverse)

/-- Mapping directions to unit coordinate steps recovers exactly the
previously verified offset-word transform. -/
theorem map_step_normalizationDirectionWord
    (sourceTemplate targetTemplate : List Cell)
    (oldDirections : List AxisDirection)
    (sourceUnitSteps :
      sourceTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (targetReverseUnitSteps :
      targetTemplate.reverse.IsChain AxisDirection.IsUnitAxisStep) :
    (normalizationDirectionWord sourceTemplate targetTemplate
        oldDirections).map AxisDirection.step =
      normalizationUnitRouteOffsets sourceTemplate targetTemplate
        (oldDirections.map AxisDirection.step) := by
  unfold normalizationDirectionWord normalizationUnitRouteOffsets
  rw [List.map_append, List.map_append]
  rw [map_routeStepDirections_step_eq_routeStepOffsets
    sourceTemplate sourceUnitSteps]
  rw [map_routeStepDirections_step_eq_routeStepOffsets
    targetTemplate.reverse targetReverseUnitSteps]
  simp

end PeriodicThreeDM
end LeanTrominoes
