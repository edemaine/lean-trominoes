/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableFans
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineTailEndpointContactSeparation

/-!
# Variable fans versus adjacent corridor macrocells

The connector-local half of a coordinated variable fan is always separated
from a legal corridor tile in a neighboring macrocell.  The selected outer
half has exactly one possible contact: its advertised physical-lane exit may
meet the same lane entering the tile one source step later.  These finite
certificates compose across the variable fan's gate join.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

private def firstTailContactCheck (first second : List Cell) : Bool :=
  first.all fun a => second.all fun b => guardedCheck (a = b)
    (decide (first.getLast? = some a ∧ RoutePointIsEndpoint second b))

private theorem firstTailContactCheck_eq_true (first second : List Cell) :
    firstTailContactCheck first second = true ↔ RoutesMeetOnlyAtFirstTail first second := by
  simp only [firstTailContactCheck, RoutesMeetOnlyAtFirstTail, List.all_eq_true,
    guardedCheck_eq_true, decide_eq_true_eq]

/-- Local connector gates avoid every legal corridor tile in an adjacent
macrocell. -/
theorem standardVariableLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute :
    ∀ (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      slot kind polarity fanColor incoming outgoing tileColor,
      incoming.IsGenuine → outgoing.IsGenuine →
      outgoing ≠ incoming.opposite →
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute slot kind polarity fanColor)
        (ribbonMacrocellRoute
          (ribbonAdjacentMacrocellOffsets.get offsetIndex)
          incoming outgoing tileColor) := by
  have checked : (finiteAll fun offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length =>
      finiteAll fun slot =>
      finiteAll fun kind =>
      finiteAll fun polarity =>
      finiteAll fun fanColor =>
      finiteAll fun incoming =>
      finiteAll fun outgoing =>
      finiteAll fun tileColor =>
      guardedCheck (incoming.IsGenuine ∧ outgoing.IsGenuine ∧ outgoing ≠ incoming.opposite)
        (segmentBoxesSeparateCheck
          (standardVariableLocalGateRoute slot kind polarity fanColor)
        (ribbonMacrocellRoute
          (ribbonAdjacentMacrocellOffsets.get offsetIndex)
          incoming outgoing tileColor))) = true := by
    decide +kernel
  intro offsetIndex slot kind polarity fanColor incoming outgoing tileColor incomingGenuine outgoingGenuine notReverse
  simp only [finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked offsetIndex slot kind polarity fanColor incoming outgoing tileColor ⟨incomingGenuine, outgoingGenuine, notReverse⟩)

/-- A selected outer variable route avoids an adjacent legal corridor tile
when it is not one source step in the selected direction, or when it is that
first tile but enters on a different physical lane.  The legal-turn premise
rules out the reverse-facing tile exit in the latter case. -/
theorem standardVariableOuterRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      slot,
      slot.index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ fanLane incoming outgoing tileColor,
        incoming.IsGenuine → outgoing.IsGenuine →
        outgoing ≠ incoming.opposite →
        ((ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid).step ∨
            incoming =
              (standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid) ∧
          (ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid).step ∨
            fanLane ≠ tileColor)) →
        RoutesStrictlyAvoidEachOther
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot fanLane)
          (ribbonMacrocellRoute
            (ribbonAdjacentMacrocellOffsets.get offsetIndex)
            incoming outgoing tileColor) := by
  have checked : (finiteAll fun templateIndex : Fin standardVariableOuterFanTemplates.length =>
      finiteAll fun offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length =>
      finiteAll fun slot =>
      finiteAll fun fanLane =>
      finiteAll fun incoming =>
      finiteAll fun outgoing =>
      finiteAll fun tileColor =>
      guardedCheck (slot.index < (standardVariableOuterFanTemplates.get templateIndex).directions.length ∧ incoming.IsGenuine ∧ outgoing.IsGenuine ∧ outgoing ≠ incoming.opposite ∧ ((ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid).step ∨
            incoming =
              (standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid) ∧
          (ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid).step ∨
            fanLane ≠ tileColor)))
        (segmentBoxesSeparateCheck
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot fanLane)
          (ribbonMacrocellRoute
            (ribbonAdjacentMacrocellOffsets.get offsetIndex)
            incoming outgoing tileColor))) = true := by
    decide +kernel
  intro templateIndex offsetIndex slot active fanLane incoming outgoing tileColor incomingGenuine outgoingGenuine notReverse separated
  simp only [finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked templateIndex offsetIndex slot fanLane incoming outgoing tileColor ⟨active, incomingGenuine, outgoingGenuine, notReverse, separated⟩)

/-- A selected outer variable route and the matching first corridor tile
are ordinarily separated; their advertised boundary contact is permitted. -/
theorem standardVariableOuterRoute_avoids_matchingRibbonMacrocellRoute :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      slot,
      slot.index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ lane outgoing,
        let direction :=
          (standardVariableOuterFanTemplates.get templateIndex).directions.getD
            slot.index .invalid
        direction.IsGenuine → outgoing.IsGenuine →
        outgoing ≠ direction.opposite →
        RoutesAvoidEachOther
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot lane)
          (ribbonMacrocellRoute direction.step direction outgoing lane) := by
  have checked : (finiteAll fun templateIndex : Fin standardVariableOuterFanTemplates.length =>
      finiteAll fun slot =>
      finiteAll fun lane =>
      finiteAll fun outgoing =>
      let direction := (standardVariableOuterFanTemplates.get templateIndex).directions.getD slot.index .invalid
      guardedCheck (slot.index < (standardVariableOuterFanTemplates.get templateIndex).directions.length ∧ direction.IsGenuine ∧ outgoing.IsGenuine ∧ outgoing ≠ direction.opposite)
        (routesAvoidEachOtherCheck
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot lane)
          (ribbonMacrocellRoute direction.step direction outgoing lane))) = true := by
    decide +kernel
  intro templateIndex slot active lane outgoing direction directionGenuine outgoingGenuine notReverse
  simp only [finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact (routesAvoidEachOtherCheck_eq_true _ _).mp
    (checked templateIndex slot lane outgoing ⟨active, directionGenuine, outgoingGenuine, notReverse⟩)

/-- Every listed contact in the matching variable-fan interface occurs at
the tail of the selected outer route. -/
theorem standardVariableOuterRoute_meets_matchingRibbonMacrocellRoute_onlyAtTail :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      slot,
      slot.index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ lane outgoing,
        let direction :=
          (standardVariableOuterFanTemplates.get templateIndex).directions.getD
            slot.index .invalid
        direction.IsGenuine → outgoing.IsGenuine →
        outgoing ≠ direction.opposite →
        RoutesMeetOnlyAtFirstTail
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot lane)
          (ribbonMacrocellRoute direction.step direction outgoing lane) := by
  have checked : (finiteAll fun templateIndex : Fin standardVariableOuterFanTemplates.length =>
      finiteAll fun slot =>
      finiteAll fun lane =>
      finiteAll fun outgoing =>
      let direction := (standardVariableOuterFanTemplates.get templateIndex).directions.getD slot.index .invalid
      guardedCheck (slot.index < (standardVariableOuterFanTemplates.get templateIndex).directions.length ∧ direction.IsGenuine ∧ outgoing.IsGenuine ∧ outgoing ≠ direction.opposite)
        (firstTailContactCheck
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot lane)
          (ribbonMacrocellRoute direction.step direction outgoing lane))) = true := by
    decide +kernel
  intro templateIndex slot active lane outgoing direction directionGenuine outgoingGenuine notReverse
  simp only [finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact (firstTailContactCheck_eq_true _ _).mp
    (checked templateIndex slot lane outgoing ⟨active, directionGenuine, outgoingGenuine, notReverse⟩)

/-- Complete coordinated variable fans avoid adjacent legal corridor tiles
away from their selected first source step, and also avoid the first tile
when it enters on a different physical lane. -/
theorem VariableRibbonFanData.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (offset : Cell)
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor)
    (separated :
      (offset ≠ (data.direction slot).step ∨
        incoming = data.direction slot) ∧
      (offset ≠ (data.direction slot).step ∨
        (data.kind slot).ribbonLaneForColor color ≠ tileColor)) :
    RoutesStrictlyAvoidEachOther
      (data.coordinatedRoute slot color)
      (ribbonMacrocellRoute offset incoming outgoing tileColor) := by
  let outer := data.outerData
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2
        offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have routeLength :
      slot.index < outer.selectedTemplate.directions.length := by
    rw [outer.selectedTemplate_directions compatible,
      outer.activeDirections_length]
    exact active
  have selectedDirection :
      outer.selectedTemplate.directions.getD slot.index .invalid =
        data.direction slot := by
    rw [outer.selectedTemplate_directions compatible]
    exact outer.activeDirections_getD slot active
  have localAvoid :=
    standardVariableLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex slot (data.kind slot) (data.polarity slot) color
      incoming outgoing tileColor
      incomingGenuine outgoingGenuine noReverse
  have outerAvoid :=
    standardVariableOuterRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
      templateIndex offsetIndex slot
      (by rw [templateEq]; exact routeLength)
      ((data.kind slot).ribbonLaneForColor color)
      incoming outgoing tileColor
      incomingGenuine outgoingGenuine noReverse (by
        rw [templateEq, offsetEq, selectedDirection]
        exact separated)
  rw [offsetEq] at localAvoid
  rw [templateEq, offsetEq] at outerAvoid
  exact localAvoid.join_left outerAvoid
    (standardVariableLocalGateRoute_getLast?
      slot (data.kind slot) (data.polarity slot) color)
    (outer.outerRoute_head? compatible slot active
      ((data.kind slot).ribbonLaneForColor color))

/-- A complete coordinated variable fan is ordinarily separated from its
matching first corridor tile.  Their only listed contact occurs at the fan's
advertised ribbon exit. -/
theorem VariableRibbonFanData.coordinatedRoute_avoids_matchingRibbonMacrocellRoute
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (outgoing : AxisDirection)
    (directionGenuine : (data.direction slot).IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ (data.direction slot).opposite) :
    RoutesAvoidEachOther
      (data.coordinatedRoute slot color)
      (ribbonMacrocellRoute
        (data.direction slot).step (data.direction slot) outgoing
        ((data.kind slot).ribbonLaneForColor color)) := by
  let outer := data.outerData
  let lane := (data.kind slot).ribbonLaneForColor color
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
  have routeLength :
      slot.index < outer.selectedTemplate.directions.length := by
    rw [outer.selectedTemplate_directions compatible,
      outer.activeDirections_length]
    exact active
  have selectedDirection :
      outer.selectedTemplate.directions.getD slot.index .invalid =
        data.direction slot := by
    rw [outer.selectedTemplate_directions compatible]
    exact outer.activeDirections_getD slot active
  have offsetAdjacent :
      RibbonMacrocellOffsetAdjacent (data.direction slot).step := by
    cases direction : data.direction slot <;>
      simp_all [RibbonMacrocellOffsetAdjacent,
        AxisDirection.IsGenuine, AxisDirection.step]
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff
        (data.direction slot).step).2 offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have localAvoid :=
    standardVariableLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex
      slot (data.kind slot) (data.polarity slot) color
      (data.direction slot) outgoing lane
      directionGenuine outgoingGenuine noReverse
  rw [offsetEq] at localAvoid
  have outerAvoid :=
    standardVariableOuterRoute_avoids_matchingRibbonMacrocellRoute
      templateIndex slot (by rw [templateEq]; exact routeLength)
      lane outgoing (by rw [templateEq, selectedDirection]; exact directionGenuine)
      outgoingGenuine (by rw [templateEq, selectedDirection]; exact noReverse)
  have outerContacts :=
    standardVariableOuterRoute_meets_matchingRibbonMacrocellRoute_onlyAtTail
      templateIndex slot (by rw [templateEq]; exact routeLength)
      lane outgoing (by rw [templateEq, selectedDirection]; exact directionGenuine)
      outgoingGenuine (by rw [templateEq, selectedDirection]; exact noReverse)
  rw [templateEq, selectedDirection] at outerAvoid outerContacts
  have assembled := RoutesAvoidEachOther.join_left_of_tail_contact
      localAvoid outerAvoid outerContacts
      (standardVariableLocalGateRoute_getLast?
        slot (data.kind slot) (data.polarity slot) color)
      (outer.outerRoute_head? compatible slot active lane)
  simpa [VariableRibbonFanData.coordinatedRoute,
    VariableOuterFanData.outerRoute, outer, lane] using assembled

/-- The advertised exit is the only listed point shared by a complete
variable fan and its matching first corridor tile. -/
theorem VariableRibbonFanData.coordinatedRoute_matchingRibbonMacrocellRoute_only_common
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (outgoing : AxisDirection)
    (directionGenuine : (data.direction slot).IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ (data.direction slot).opposite) :
    ∀ point,
      point ∈ data.coordinatedRoute slot color →
      point ∈ ribbonMacrocellRoute
        (data.direction slot).step (data.direction slot) outgoing
        ((data.kind slot).ribbonLaneForColor color) →
      point = standardRibbonMacrocellExit
        (data.direction slot) ((data.kind slot).ribbonLaneForColor color) := by
  let outer := data.outerData
  let lane := (data.kind slot).ribbonLaneForColor color
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
  have routeLength :
      slot.index < outer.selectedTemplate.directions.length := by
    rw [outer.selectedTemplate_directions compatible,
      outer.activeDirections_length]
    exact active
  have selectedDirection :
      outer.selectedTemplate.directions.getD slot.index .invalid =
        data.direction slot := by
    rw [outer.selectedTemplate_directions compatible]
    exact outer.activeDirections_getD slot active
  have offsetAdjacent :
      RibbonMacrocellOffsetAdjacent (data.direction slot).step := by
    cases direction : data.direction slot <;>
      simp_all [RibbonMacrocellOffsetAdjacent,
        AxisDirection.IsGenuine, AxisDirection.step]
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff
        (data.direction slot).step).2 offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have localAvoid :=
    standardVariableLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex
      slot (data.kind slot) (data.polarity slot) color
      (data.direction slot) outgoing lane
      directionGenuine outgoingGenuine noReverse
  rw [offsetEq] at localAvoid
  have outerContacts :=
    standardVariableOuterRoute_meets_matchingRibbonMacrocellRoute_onlyAtTail
      templateIndex slot (by rw [templateEq]; exact routeLength)
      lane outgoing (by rw [templateEq, selectedDirection]; exact directionGenuine)
      outgoingGenuine (by rw [templateEq, selectedDirection]; exact noReverse)
  rw [templateEq, selectedDirection] at outerContacts
  intro point fanMember tileMember
  change point ∈ joinAtEndpoint
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) color)
      (outer.outerRoute slot lane) at fanMember
  rcases mem_joinAtEndpoint fanMember with localMember | outerMember
  · exact (localAvoid.2.2.2 point localMember point tileMember rfl).elim
  · have tail := outerContacts point outerMember point tileMember rfl
    have joinedLast :
        (data.coordinatedRoute slot color).getLast? = some point := by
      exact joinAtEndpoint_getLast?
        (standardVariableLocalGateRoute_getLast?
          slot (data.kind slot) (data.polarity slot) color)
        (outer.outerRoute_head? compatible slot active lane)
        tail.1
    exact Option.some.inj
      (joinedLast.symm.trans
        (data.coordinatedRoute_getLast?
          compatible slot active color))

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
