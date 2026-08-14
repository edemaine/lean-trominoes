/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseRouteStep

/-!
# Reverse strip-orientation values along complete normalized routes
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- The oriented half-edge value at `before` pointing along a normalized
strip route toward its successor `after`. -/
def PlanarPresentation.stripDrawingRouteValue
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation)
    (before after translate : Cell) : Bool :=
  orientation
    (Cell.add
      (stripReflectedLocation presentation.finalNormalizationPeriod before)
      (presentation.stripPeriodTranslation translate))
    (Side.ofAxisDirection (AxisDirection.between before after))

/-- The one-cell strip theorem expressed using directed-pair route values. -/
theorem ContinuousPlanarPresentation.stripDrawingRouteValue_window
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (leading : List Cell) (before current after : Cell) (rest : List Cell)
    (routeEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest)
    (translate : Cell) :
    presentation.toPlanarPresentation.stripDrawingRouteValue orientation
        current after translate =
      presentation.toPlanarPresentation.stripDrawingRouteValue orientation
        before current translate := by
  simpa [PlanarPresentation.stripDrawingRouteValue] using
    presentation.stripDrawingOrientation_routeWindow_forward_eq_predecessor
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        edgeMember leading before current after rest routeEquation translate

/-- Two presentations of a list as a prefix followed by a final pair have
the same final pair. -/
theorem List.lastPair_eq_of_strip_append_pair_eq
    {α : Type*} (firstPrefix secondPrefix : List α)
    (first second third fourth : α)
    (equal :
      firstPrefix ++ [first, second] = secondPrefix ++ [third, fourth]) :
    first = third ∧ second = fourth := by
  have reverseEqual := congrArg List.reverse equal
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append] at reverseEqual
  injection reverseEqual with secondEqual tailsEqual
  injection tailsEqual with firstEqual
  exact ⟨firstEqual, secondEqual⟩

/-- Iterating the strip route-window law from any displayed pair reaches the
fixed final pair of the same route. -/
theorem ContinuousPlanarPresentation.stripDrawingRouteValue_eq_finalAux
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (targetLeading : List Cell) (targetBefore target : Cell)
    (targetEquation :
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        targetLeading ++ [targetBefore, target])
    (translate : Cell) :
    ∀ (rest : List Cell) (leading : List Cell)
      (before current after : Cell),
      presentation.toPlanarPresentation.finalNormalizationRoute edge =
        leading ++ before :: current :: after :: rest →
      presentation.toPlanarPresentation.stripDrawingRouteValue orientation
          before current translate =
        presentation.toPlanarPresentation.stripDrawingRouteValue orientation
          targetBefore target translate := by
  intro rest
  induction rest with
  | nil =>
      intro leading before current after routeEquation
      have finalPairs : current = targetBefore ∧ after = target := by
        apply List.lastPair_eq_of_strip_append_pair_eq
          (leading ++ [before]) targetLeading current after
            targetBefore target
        calc
          (leading ++ [before]) ++ [current, after] =
              leading ++ before :: current :: after :: [] := by simp
          _ = presentation.toPlanarPresentation.finalNormalizationRoute edge :=
            routeEquation.symm
          _ = targetLeading ++ [targetBefore, target] := targetEquation
      have window := presentation.stripDrawingRouteValue_window
        wellFormed degree horizontal sourceInside collisionFree orientation valid
          edgeMember leading before current after [] routeEquation translate
      calc
        presentation.toPlanarPresentation.stripDrawingRouteValue orientation
            before current translate =
            presentation.toPlanarPresentation.stripDrawingRouteValue orientation
              current after translate := window.symm
        _ = presentation.toPlanarPresentation.stripDrawingRouteValue orientation
              targetBefore target translate := by
          rw [finalPairs.1, finalPairs.2]
  | cons next tail induction =>
      intro leading before current after routeEquation
      have window := presentation.stripDrawingRouteValue_window
        wellFormed degree horizontal sourceInside collisionFree orientation valid
          edgeMember leading before current after (next :: tail) routeEquation
            translate
      have nextEquation :
          presentation.toPlanarPresentation.finalNormalizationRoute edge =
            (leading ++ [before]) ++ current :: after :: next :: tail := by
        rw [routeEquation]
        simp
      exact window.symm.trans
        (induction (leading ++ [before]) current after next nextEquation)

end PeriodicThreeDM

end LeanTrominoes
