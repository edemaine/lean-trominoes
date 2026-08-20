/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # Contracted triple endpoints retain their incidence directions -/

namespace LeanTrominoes

open Gadget PeriodicOrthocrossing

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- `joinPolylines` retains the first two points of a nondegenerate first
route. -/
theorem polylineFirstDirection_joinPolylines_of_length_ge_two
    {first second : List Cell} (length : 2 ≤ first.length) :
    AxisDirection.polylineFirstDirection
        (joinPolylines first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons next rest =>
          simp [joinPolylines,
            AxisDirection.polylineFirstDirection]

/-- At the source of a retained edge, the contracted outward direction is
definitionally the first direction of the represented incidence route. -/
@[simp] theorem outwardDirection_source_retained
    (input : Input) (color : WireColor) (atom : Nat)
    (incidence : Incidence) :
    outwardDirection input
        (.source (.retained color atom incidence)) =
      AxisDirection.polylineFirstDirection
        (incidenceRoute input ⟨incidence.tripleIndex, color⟩) := by
  rfl

/-- Joining the reverse incidence at a suppressed element does not change
the first direction at the first triple endpoint. -/
theorem outwardDirection_source_through
    (input : Input) (color : WireColor) (atom : Nat)
    (first second : Incidence)
    (firstLength :
      2 ≤ (incidenceRoute input
        ⟨first.tripleIndex, color⟩).length) :
    outwardDirection input
        (.source (.through color atom first second)) =
      AxisDirection.polylineFirstDirection
        (incidenceRoute input ⟨first.tripleIndex, color⟩) := by
  unfold outwardDirection contractedEdgeRoute
  exact polylineFirstDirection_joinPolylines_of_length_ge_two firstLength

/-- At the second triple endpoint of a suppressed edge, reversing the second
incidence and then reading the contracted target outward recovers the first
direction of that original incidence. -/
theorem outwardDirection_target_through
    (input : Input) (color : WireColor) (atom : Nat)
    (first second : Incidence) (middle : Cell)
    (firstLast :
      (incidenceRoute input ⟨first.tripleIndex, color⟩).getLast? =
        some middle)
    (secondHead :
      (reversedIncidenceRouteAt input color first second).head? =
        some middle)
    (secondLength :
      2 ≤ (incidenceRoute input
        ⟨second.tripleIndex, color⟩).length) :
    outwardDirection input
        (.target (.through color atom first second)) =
      AxisDirection.polylineFirstDirection
        (incidenceRoute input ⟨second.tripleIndex, color⟩) := by
  have reversedLength :
      2 ≤ (reversedIncidenceRouteAt input color first second).length := by
    simpa only [reversedIncidenceRouteAt, List.length_reverse,
      translatePolyline, List.length_map] using secondLength
  unfold outwardDirection contractedEdgeRoute
  change
    (AxisDirection.polylineLastDirection
      (joinAtEndpoint
        (incidenceRoute input ⟨first.tripleIndex, color⟩)
        (reversedIncidenceRouteAt input color first second))).opposite = _
  rw [AxisDirection.polylineLastDirection_joinAtEndpoint
    firstLast secondHead reversedLength]
  simp [reversedIncidenceRouteAt]

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
