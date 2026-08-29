/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineNormalizationDirectionExtensionality
import LeanTrominoes.RetainedAngularFanFallbackExteriorRadialDirectionSemantics
import LeanTrominoes.RetainedAngularFanFallbackNormalizedTerminalTailData
import LeanTrominoes.RetainedAngularFanFallbackSuffixOuterDirectionSemantics

/-! # Normalization invariance of the final radial split -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler

private theorem retainedTerminalFanOuterRadialFinalStubAt_zero_directions :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      Gadget.unitSubdivisionDirections
          (retainedTerminalFanOuterRadialFinalStubAt
            (0, 0) direction slot) =
        inwardRayUnitDirections direction := by
  native_decide

/-- Every positioned final radial primitive has the common one-block inward
direction word selected by its terminal direction. -/
theorem retainedTerminalFanOuterRadialFinalStubAt_directions
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterRadialFinalStubAt
          center direction slot) =
      inwardRayUnitDirections direction := by
  have translated :=
    retainedTerminalFanOuterRadialFinalStubAt_translatePolyline
      center (0, 0) direction slot
  simp only [Cell.add_zero] at translated
  rw [← translated,
    Gadget.unitSubdivisionDirections_translatePolyline]
  exact retainedTerminalFanOuterRadialFinalStubAt_zero_directions
    direction slot

/-- A positive repeated radial word splits into all but its final primitive
block followed by that one fixed block. -/
theorem radialCopies_eq_pred_append
    (count : Nat)
    (direction : RetainedTerminalDirection)
    (positive : 0 < count) :
    radialCopies count direction =
      radialCopies (count - 1) direction ++
        inwardRayUnitDirections direction := by
  cases count with
  | zero => omega
  | succ count =>
      simp [radialCopies, List.replicate_succ']

/-- Explicitly separating the final primitive block does not change the
normalization of a positive radial route.  This covers blocked staircases by
equality and cardinal rays by their identical start and unit-direction word. -/
theorem retainedTerminalFanOuterRadialRoute_normalize_eq_split
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    AxisDirection.normalizeOrthogonalPolyline
        (retainedTerminalFanOuterRadialRoute center terminal slot) =
      AxisDirection.normalizeOrthogonalPolyline
        (splitRadialRoute center terminal slot) := by
  let radialRoute :=
    retainedTerminalFanOuterRadialRoute center terminal slot
  let radialPrefix :=
    retainedTerminalFanOuterRadialPrefix center terminal slot
  let finalStub :=
    retainedTerminalFanOuterRadialFinalStubAt
      center terminal.1 slot
  let splitRoute := splitRadialRoute center terminal slot
  have radialRouteHead :
      radialRoute.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedTerminalFanOuterRadialRoute_head? center terminal slot
  have radialRouteNonempty : radialRoute ≠ [] := by
    intro empty
    rw [empty] at radialRouteHead
    simp at radialRouteHead
  have radialPrefixHead :
      radialPrefix.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedTerminalFanOuterRadialPrefix_head? center terminal slot
  have radialPrefixNonempty : radialPrefix ≠ [] := by
    intro empty
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  have splitRouteHead :
      splitRoute.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate := by
    unfold splitRoute splitRadialRoute
    exact joinAtEndpoint_head? radialPrefixHead
  have splitRouteNonempty : splitRoute ≠ [] := by
    intro empty
    rw [empty] at splitRouteHead
    simp at splitRouteHead
  have radialRouteOrthogonal : OrthogonalPolyline radialRoute :=
    retainedTerminalFanOuterRadialRoute_orthogonal
      center terminal slot
  have radialPrefixOrthogonal : OrthogonalPolyline radialPrefix :=
    retainedTerminalFanOuterRadialPrefix_orthogonal
      center terminal slot
  have finalStubOrthogonal : OrthogonalPolyline finalStub :=
    retainedTerminalFanOuterRadialFinalStubAt_orthogonal
      center terminal.1 slot
  have splitRouteOrthogonal : OrthogonalPolyline splitRoute := by
    unfold splitRoute splitRadialRoute
    exact radialPrefixOrthogonal.joinAtEndpoint
      finalStubOrthogonal
      (retainedTerminalFanOuterRadialPrefix_getLast?
        center terminal slot radialPositive)
      (retainedTerminalFanOuterRadialFinalStubAt_head?
        center terminal.1 slot)
  apply
    AxisDirection.normalizeOrthogonalPolyline_eq_of_head?_eq_of_directions_eq
      radialRouteNonempty splitRouteNonempty
      radialRouteOrthogonal splitRouteOrthogonal
  · rw [radialRouteHead, splitRouteHead]
  · rw [retainedTerminalFanOuterRadialRoute_directions]
    unfold splitRoute splitRadialRoute
    rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
    · rw [retainedTerminalFanOuterRadialPrefix_directions,
        retainedTerminalFanOuterRadialFinalStubAt_directions,
        radialCopies_eq_pred_append
          (retainedTerminalFanOuterRadialLength terminal)
          terminal.1 radialPositive]
      simp [List.append_assoc]
    · exact radialPrefixNonempty
    · rw [retainedTerminalFanOuterRadialPrefix_getLast?
          center terminal slot radialPositive,
        retainedTerminalFanOuterRadialFinalStubAt_head?]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
