/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceData
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalDirectionNonempty
import LeanTrominoes.GadgetSparseRouteDirectionEndpoints

/-! # Endpoint directions of completed Figure 9 route headers -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeader

open Gadget PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
open PlanarOneInThreeNoUnitsFigureNine

/-- Completing an inherited route's dynamic tail preserves its first
direction. Polarity refinement leaves at least one prefix edge even when
the complement-original operation drops two edges. -/
theorem outputFirstDirection_eq_completed
    (header : Header) (tail : List AxisDirection) :
    outputFirstDirection header =
      ((block header tail).directions
        RetainedFigureNineRouteDirectionBlock.directions).headD .invalid := by
  rcases header with ⟨⟨slot, operation⟩, figurePrefix⟩
  cases figurePrefix with
  | «local» query => rfl
  | inherited direction query =>
      obtain ⟨first, rest, prefixEq⟩ := List.exists_cons_of_ne_nil
        (normalizedLocalExtendedDirectionBlock_ne_nil query)
      cases operation <;>
        simp [outputFirstDirection, block, operationBlock,
          RouteDirectionBlock.directions,
          RetainedFigureNineRouteDirectionBlock.directions,
          prefixEq, refinementFactor, repeatDirections, reverseDirections,
          List.replicate_succ]

/-- Variable fans depart along the reversed stored route. Their direction
is the opposite of the completed route's last edge, including its tail. -/
def completeOccurrenceData (header : Header) (tail : List AxisDirection) :
    OccurrenceData :=
  { occurrenceData header with
    direction := (((block header tail).directions
      RetainedFigureNineRouteDirectionBlock.directions).getLastD .invalid).opposite }

@[simp] theorem completeOccurrenceData_atomControl
    (header : Header) (tail : List AxisDirection) :
    (completeOccurrenceData header tail).atomControl = outputAtomControl header := rfl

@[simp] theorem completeOccurrenceData_kind
    (header : Header) (tail : List AxisDirection) :
    (completeOccurrenceData header tail).kind = outputConnectorKind header := rfl

@[simp] theorem completeOccurrenceData_polarity
    (header : Header) (tail : List AxisDirection) :
    (completeOccurrenceData header tail).polarity = outputPolarity header := rfl

private theorem repeatThree_cons (first : AxisDirection)
    (rest : List AxisDirection) :
    repeatDirections 3 (first :: rest) =
      first :: first :: first :: repeatDirections 3 rest := by
  simp [repeatDirections, List.replicate_succ]

/-- The final direction needs only the tail's last symbol. This permits a
finite-state compiler even when the actual route tail is unbounded. -/
theorem completeOccurrenceData_eq_lastTail
    (header : Header) (tail : List AxisDirection) :
    completeOccurrenceData header tail =
      completeOccurrenceData header tail.getLast?.toList := by
  rcases header with ⟨⟨slot, operation⟩, figurePrefix⟩
  cases figurePrefix with
  | «local» query => rfl
  | inherited direction query =>
      obtain ⟨first, rest, prefixEq⟩ := List.exists_cons_of_ne_nil
        (normalizedLocalExtendedDirectionBlock_ne_nil query)
      induction tail using List.reverseRecOn with
      | nil => rfl
      | append_singleton tail last induction =>
          cases operation <;>
            simp [completeOccurrenceData, block, operationBlock,
              RouteDirectionBlock.directions,
              RetainedFigureNineRouteDirectionBlock.directions,
              prefixEq, refinementFactor, repeatThree_cons,
              reverseDirections, List.getLast?_cons, List.getLast?_append,
              repeatDirections_getLast?]

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeader
