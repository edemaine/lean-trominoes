/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidencePrefixLength
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # First directions of horizontal variable incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Appending a tail after a nondegenerate prefix does not change the first
directed edge. -/
theorem polylineFirstDirection_joinAtEndpoint_left_of_length_ge_two
    (first second : List Cell) (length : 2 ≤ first.length) :
    AxisDirection.polylineFirstDirection (joinAtEndpoint first second) =
      AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          simp [joinAtEndpoint, AxisDirection.polylineFirstDirection]

/-- Once its local prefix has an edge, a variable incidence's optional
source-to-clause tail cannot alter its first direction. -/
theorem horizontalVariableTypedIncidenceRouteComputed_firstDirection_of_prefix_length
    (input : HorizontalVariableTypedIncidenceRouteInput)
    (prefixLength :
      2 ≤ (horizontalVariableIncidencePrefixComputed
        (horizontalVariableRoutePrefixQueryComputed input)).length) :
    AxisDirection.polylineFirstDirection
        (horizontalVariableTypedIncidenceRouteComputed input) =
      AxisDirection.polylineFirstDirection
        (horizontalVariableIncidencePrefixComputed
          (horizontalVariableRoutePrefixQueryComputed input)) := by
  unfold horizontalVariableTypedIncidenceRouteComputed
  split
  · exact polylineFirstDirection_joinAtEndpoint_left_of_length_ge_two
      _ _ prefixLength
  · rfl

/-- Translating a local variable-site route into its macrocell does not
change its first direction. -/
theorem horizontalVariableIncidencePrefixComputed_firstDirection
    (input : HorizontalVariableIncidencePrefixInput) :
    AxisDirection.polylineFirstDirection
        (horizontalVariableIncidencePrefixComputed input) =
      AxisDirection.polylineFirstDirection
        (horizontalVariableIncidenceLocalRouteComputed input) := by
  simp [horizontalVariableIncidencePrefixComputed]

/-- Every complete ordinary variable incidence has the first direction of
its finite local variable-site table entry. -/
theorem horizontalOrdinaryVariableTypedIncidenceRouteComputed_firstDirection
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member : Triple.ordinary atom slot variant localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    AxisDirection.polylineFirstDirection
        (horizontalVariableTypedIncidenceRouteComputed
          ((((source, atom), slot),
            Triple.ordinary atom slot variant localTriple), color)) =
      AxisDirection.polylineFirstDirection
        (horizontalVariableIncidenceLocalRouteComputed
          (((source, atom),
            Triple.ordinary atom slot variant localTriple), color)) := by
  rw [horizontalVariableTypedIncidenceRouteComputed_firstDirection_of_prefix_length]
  · exact horizontalVariableIncidencePrefixComputed_firstDirection _
  · exact horizontalOrdinaryVariableIncidencePrefixComputed_length_ge_two
      source atom slot variant localTriple member color

/-- Every complete fixed-red variable incidence has the first direction of
its finite local variable-site table entry. -/
theorem horizontalFixedRedVariableTypedIncidenceRouteComputed_firstDirection
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member : Triple.fixedRed atom slot localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    AxisDirection.polylineFirstDirection
        (horizontalVariableTypedIncidenceRouteComputed
          ((((source, atom), slot),
            Triple.fixedRed atom slot localTriple), color)) =
      AxisDirection.polylineFirstDirection
        (horizontalVariableIncidenceLocalRouteComputed
          (((source, atom), Triple.fixedRed atom slot localTriple), color)) := by
  rw [horizontalVariableTypedIncidenceRouteComputed_firstDirection_of_prefix_length]
  · exact horizontalVariableIncidencePrefixComputed_firstDirection _
  · exact horizontalFixedRedVariableIncidencePrefixComputed_length_ge_two
      source atom slot localTriple member color

end PeriodicCNFStripReduction
end LeanTrominoes
