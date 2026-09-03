/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalTypedShapeData
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceDirectionBlockData

/-! # Horizontal direction-block form of grouped variable incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The raw finite query used by the local typed shape is the extracted
horizontal variable-prefix query. -/
theorem groupedVariableIncidenceTypedPrefixDirection_eq_horizontal
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (triple : Triple RoutedVariable) (color : WireColor) :
    HorizontalFiniteIncidenceDirectionQuery.directions
        (.variable
          (horizontalOccurrenceVariableRibbonFanDataComputed (source, atom))
          (variableSiteTripleOfTyped triple) color) =
      horizontalVariableIncidencePrefixDirections
        (((source, atom), triple), color) := by
  simpa only [horizontalVariableIncidenceLocalRouteInputComputed] using
    HorizontalFiniteIncidenceDirectionQuery.directions_variable_input
      (((source, atom), triple), color)

@[simp] theorem horizontalVariableRoutePrefixQueryComputed_explicit
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (triple : Triple RoutedVariable) (color : WireColor) :
    horizontalVariableRoutePrefixQueryComputed
        ((((source, atom), slot), triple), color) =
      (((source, atom), triple), color) :=
  rfl

@[simp] theorem horizontalVariableOccurrenceRouteQueryComputed_explicit
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (triple : Triple RoutedVariable) (color : WireColor) :
    horizontalVariableOccurrenceRouteQueryComputed
        ((((source, atom), slot), triple), color) =
      (((source, atom), slot), color) :=
  rfl

/-- Pointwise form of the typed shape/direction-block correspondence. -/
theorem groupedVariableIncidenceTypedShapeBody_eq_directionBlock
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (triple : Triple RoutedVariable) (color : WireColor)
    (routeBlock : HorizontalRoutedRouteDirectionBlock)
    (routedBody : List AxisDirection)
    (routedBodyEq : routedBody =
      horizontalOccurrenceCoordinatedDirections
        (((source, atom), slot), color) routeBlock) :
    HorizontalFiniteIncidenceDirectionQuery.directions
          (.variable
            (horizontalOccurrenceVariableRibbonFanDataComputed (source, atom))
            (variableSiteTripleOfTyped triple) color) ++
        (if triple = routedOccurrenceTriple
            (horizontalNormalizedRoutedFormulaComputed source).erase
            atom slot color then routedBody else []) =
      horizontalVariableTypedIncidenceDirections
        ((((source, atom), slot), triple), color)
        (if triple = routedOccurrenceTriple
            (horizontalNormalizedRoutedFormulaComputed source).erase
            atom slot color then .routed routeBlock else .local) := by
  by_cases routed : triple =
      routedOccurrenceTriple
        (horizontalNormalizedRoutedFormulaComputed source).erase
        atom slot color
  · simp only [if_pos routed,
      horizontalVariableTypedIncidenceDirections]
    rw [groupedVariableIncidenceTypedPrefixDirection_eq_horizontal,
      routedBodyEq, horizontalVariableRoutePrefixQueryComputed_explicit,
      horizontalVariableOccurrenceRouteQueryComputed_explicit]
  · simp only [if_neg routed,
      horizontalVariableTypedIncidenceDirections, List.append_nil]
    exact groupedVariableIncidenceTypedPrefixDirection_eq_horizontal
      source atom triple color

/-- The typed occurrence block interpreted using an explicitly chosen compact
coordinated route block for each color. -/
def horizontalGroupedVariableTypedIncidenceDirectionBlockBodies
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (routeBlock : WireColor → HorizontalRoutedRouteDirectionBlock) :
    List (List AxisDirection) :=
  let normalized := (horizontalNormalizedRoutedFormulaComputed source).erase
  (occurrenceTriples normalized atom slot).flatMap fun triple =>
    incidenceColors.map fun color =>
      let input : HorizontalVariableTypedIncidenceRouteInput :=
        ((((source, atom), slot), triple), color)
      horizontalVariableTypedIncidenceDirections input
        (if triple = routedOccurrenceTriple normalized atom slot color then
          .routed (routeBlock color)
        else
          .local)

/-- Replacing every abstract routed suffix by its compact coordinated word
turns the local typed shape into the horizontal direction-block presentation. -/
theorem groupedVariableIncidenceTypedShapeBodies_eq_directionBlocks
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (routeBlock : WireColor → HorizontalRoutedRouteDirectionBlock)
    (routedBody : WireColor → List AxisDirection)
    (routedBodyEq : ∀ color,
      routedBody color =
        horizontalOccurrenceCoordinatedDirections
          (((source, atom), slot), color) (routeBlock color)) :
    groupedVariableIncidenceTypedShapeBodies
        (horizontalNormalizedRoutedFormulaComputed source).erase
        atom slot
        (horizontalOccurrenceVariableRibbonFanDataComputed (source, atom))
        routedBody =
      horizontalGroupedVariableTypedIncidenceDirectionBlockBodies
        source atom slot routeBlock := by
  unfold groupedVariableIncidenceTypedShapeBodies
    horizontalGroupedVariableTypedIncidenceDirectionBlockBodies
  apply List.flatMap_congr
  intro triple _tripleMember
  apply List.map_congr_left
  intro color _colorMember
  exact groupedVariableIncidenceTypedShapeBody_eq_directionBlock
    source atom slot triple color (routeBlock color) (routedBody color)
    (routedBodyEq color)

end LeanTrominoes.PeriodicCNFStripReduction

end
