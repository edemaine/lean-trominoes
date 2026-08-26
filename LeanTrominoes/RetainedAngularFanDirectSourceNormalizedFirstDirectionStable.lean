/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceCompleteFigure7HeadIsolation

/-! # Slot independence of normalized direct-source first directions -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

private theorem polylineFirstDirection_joinAtEndpoint_of_genuine
    {first second : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection first).IsGenuine) :
    AxisDirection.polylineFirstDirection (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => rfl

private theorem two_le_length_of_firstDirection_isGenuine
    {points : List Cell}
    (genuine :
      (AxisDirection.polylineFirstDirection points).IsGenuine) :
    2 ≤ points.length := by
  cases points with
  | nil =>
      simp [AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine] at genuine
      | cons second rest => simp

/-- Loop erasure preserves the finite coordinated direct-source direction;
in particular the normalized first direction does not depend on the
variable-side occurrence slot. -/
theorem retainedDirectSourceNormalizedFirstDirection_eq_coordinated
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    retainedDirectSourceNormalizedFirstDirection kind index slot =
      retainedDirectSourceCoordinatedFirstDirection kind index := by
  let choice := retainedDirectSourceZeroChoice kind index
  let route := choice.completeFigure7Route slot
  have prefixDirection :
      AxisDirection.polylineFirstDirection (choice.completeRoute slot) =
        retainedDirectSourceCoordinatedFirstDirection kind index := by
    simpa [choice, retainedDirectSourceZeroChoice] using
      choice.completeRoute_firstDirection slot
  have prefixGenuine :
      (AxisDirection.polylineFirstDirection
        (choice.completeRoute slot)).IsGenuine := by
    rw [prefixDirection]
    exact retainedDirectSourceCoordinatedFirstDirection_isGenuine
      kind index
  have routeDirection :
      AxisDirection.polylineFirstDirection route =
        retainedDirectSourceCoordinatedFirstDirection kind index := by
    change
      AxisDirection.polylineFirstDirection
          (joinAtEndpoint (choice.completeRoute slot)
            (choice.figure7Spoke slot)) = _
    exact
      (polylineFirstDirection_joinAtEndpoint_of_genuine
        prefixGenuine).trans prefixDirection
  have routeGenuine :
      (AxisDirection.polylineFirstDirection route).IsGenuine := by
    rw [routeDirection]
    exact retainedDirectSourceCoordinatedFirstDirection_isGenuine
      kind index
  have routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline route := by
    simpa [route, choice] using
      (retainedDirectSourceZeroCompleteFigure7Route_valid
        kind index slot).2
  have routeLength : 2 ≤ route.length :=
    two_le_length_of_firstDirection_isGenuine routeGenuine
  unfold retainedDirectSourceNormalizedFirstDirection
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline route) = _
  calc
    _ = AxisDirection.polylineFirstDirection route :=
      AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
        (AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
          routeLength routeOrthogonal)
        routeOrthogonal
        (by
          simpa [route, choice] using
            retainedDirectSourceZeroCompleteFigure7Route_headNotInTail
              kind index slot)
    _ = retainedDirectSourceCoordinatedFirstDirection kind index :=
      routeDirection

end PeriodicEightOccurrenceSplit
end LeanTrominoes
