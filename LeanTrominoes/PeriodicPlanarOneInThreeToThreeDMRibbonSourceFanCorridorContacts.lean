/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCorridorSimplicity
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoreClauseSeparation

/-!
# Same-strand source fan/corridor contacts

The finite matching-interface checks are translated to the actual source
macrocells.  At either end of an occurrence route, the endpoint fan and the
adjacent same-colored corridor tile are continuously separated and share
only their advertised boundary point.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Translation preserves the simplicity of a coordinated source variable
fan. -/
theorem occurrenceCoordinatedRibbonVariableStub_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  exact routeIsSimple_translate
    (data.coordinatedRoute_simple
      (compatible.1 entry) slot active color)
    (ribbonMacrocellOrigin (placement.position entry.1.1))

/-- Translation preserves the simplicity of a coordinated source clause
fan. -/
theorem occurrenceCoordinatedRibbonClauseStub_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (occurrenceCoordinatedRibbonClauseStub
        presentation entry color) := by
  let target := occurrenceSourceClauseTarget presentation entry
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData presentation clauseIndex
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry color
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      presentation clauseIndex entry entry.mem_activeClauseOccurrenceEntries
  exact routeIsSimple_translate
    (data.coordinatedRoute_simple
      (compatible.2 entry) group active lane)
    (ribbonMacrocellOrigin target)

/-- The coordinated variable fan is ordinarily separated from the first
same-colored corridor tile. -/
theorem occurrenceCoordinatedRibbonVariableStub_avoids_firstRibbonMacrocellRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (first next : Cell)
    (rest : List Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        placement.position entry.1.1 :: first :: next :: rest)
    (unitSteps :
      (placement.position entry.1.1 :: first :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (placement.position entry.1.1 :: first :: next :: rest)) :
    RoutesAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry color)
      (ribbonMacrocellRoute first
        (AxisDirection.between (placement.position entry.1.1) first)
        (AxisDirection.between first next)
        (routedRibbonLane source.erase entry color)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let center := placement.position entry.1.1
  let data := sourceVariableRibbonFanData planar entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let lane := routedRibbonLane source.erase entry color
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      planar entry
  have parts := unitSteps_cons_cons_cons unitSteps
  have directionEq :
      AxisDirection.between center first = data.direction slot := by
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_direction]
    simp [center, planar, occurrenceSourceVariableDirection,
      routeEquation]
  have physicalLaneEq :
      (data.kind slot).ribbonLaneForColor color = lane := by
    exact
      VariableRibbonFanData.sourceVariableRibbonFanData_ribbonLaneForColor_of_same_atom
        planar entry entry rfl color
  have localAvoid :=
    data.coordinatedRoute_avoids_matchingRibbonMacrocellRoute
      (compatible.1 entry) slot active color
      (AxisDirection.between first next)
      (by
        rw [← directionEq]
        exact AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
      (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
      (by
        rw [← directionEq]
        exact noReversal.1)
  have translatedAvoid :=
    routesAvoidEachOther_translate localAvoid
      (ribbonMacrocellOrigin center)
  have firstEq :
      first = Cell.add center (data.direction slot).step := by
    rw [← directionEq]
    exact AxisDirection.add_between_step_eq_of_unitAxisStep parts.1
  have tileTranslation :
      translatePolyline (ribbonMacrocellOrigin center)
          (ribbonMacrocellRoute (data.direction slot).step
            (data.direction slot) (AxisDirection.between first next)
            ((data.kind slot).ribbonLaneForColor color)) =
        ribbonMacrocellRoute first
          (AxisDirection.between center first)
          (AxisDirection.between first next) lane := by
    unfold translatePolyline
    rw [← ribbonMacrocellRoute_add_center, ← firstEq,
      ← directionEq, physicalLaneEq]
  change RoutesAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin center)
        (data.coordinatedRoute slot color))
      (translatePolyline (ribbonMacrocellOrigin center)
        (ribbonMacrocellRoute (data.direction slot).step
          (data.direction slot) (AxisDirection.between first next)
          ((data.kind slot).ribbonLaneForColor color))) at translatedAvoid
  rw [tileTranslation] at translatedAvoid
  simpa [occurrenceCoordinatedRibbonVariableStub,
    planar, center, data, slot] using translatedAvoid

/-- The first corridor boundary is the only listed point shared by the
coordinated variable fan and its matching same-colored tile. -/
theorem occurrenceCoordinatedRibbonVariableStub_firstRibbonMacrocellRoute_only_common
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (first next : Cell)
    (rest : List Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        placement.position entry.1.1 :: first :: next :: rest)
    (unitSteps :
      (placement.position entry.1.1 :: first :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (placement.position entry.1.1 :: first :: next :: rest)) :
    ∀ point,
      point ∈ occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry color →
      point ∈ ribbonMacrocellRoute first
        (AxisDirection.between (placement.position entry.1.1) first)
        (AxisDirection.between first next)
        (routedRibbonLane source.erase entry color) →
      point = ribbonMacrocellExit
        (placement.position entry.1.1)
        (AxisDirection.between (placement.position entry.1.1) first)
        (routedRibbonLane source.erase entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  let center := placement.position entry.1.1
  let data := sourceVariableRibbonFanData planar entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let lane := routedRibbonLane source.erase entry color
  let origin := ribbonMacrocellOrigin center
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      planar entry
  have parts := unitSteps_cons_cons_cons unitSteps
  have directionEq :
      AxisDirection.between center first = data.direction slot := by
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_direction]
    simp [center, planar, occurrenceSourceVariableDirection,
      routeEquation]
  have physicalLaneEq :
      (data.kind slot).ribbonLaneForColor color = lane :=
    VariableRibbonFanData.sourceVariableRibbonFanData_ribbonLaneForColor_of_same_atom
      planar entry entry rfl color
  have localOnly :=
    data.coordinatedRoute_matchingRibbonMacrocellRoute_only_common
      (compatible.1 entry) slot active color
      (AxisDirection.between first next)
      (by
        rw [← directionEq]
        exact AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
      (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
      (by
        rw [← directionEq]
        exact noReversal.1)
  have firstEq :
      first = Cell.add center (data.direction slot).step := by
    rw [← directionEq]
    exact AxisDirection.add_between_step_eq_of_unitAxisStep parts.1
  have tileTranslation :
      translatePolyline origin
          (ribbonMacrocellRoute (data.direction slot).step
            (data.direction slot) (AxisDirection.between first next)
            ((data.kind slot).ribbonLaneForColor color)) =
        ribbonMacrocellRoute first
          (AxisDirection.between center first)
          (AxisDirection.between first next) lane := by
    unfold translatePolyline
    rw [← ribbonMacrocellRoute_add_center, ← firstEq,
      ← directionEq, physicalLaneEq]
  intro point fanMember tileMember
  have fanMember' :
      point ∈ translatePolyline origin (data.coordinatedRoute slot color) := by
    simpa [occurrenceCoordinatedRibbonVariableStub,
      planar, center, data, slot, origin] using fanMember
  have tileMember' :
      point ∈ translatePolyline origin
        (ribbonMacrocellRoute (data.direction slot).step
          (data.direction slot) (AxisDirection.between first next)
          ((data.kind slot).ribbonLaneForColor color)) := by
    rw [tileTranslation]
    exact tileMember
  rcases List.mem_map.mp fanMember' with
    ⟨fanPoint, fanPointMember, fanPointEq⟩
  rcases List.mem_map.mp tileMember' with
    ⟨tilePoint, tilePointMember, tilePointEq⟩
  have pointsEq : fanPoint = tilePoint :=
    cell_add_left_injective origin
      (fanPointEq.trans tilePointEq.symm)
  have localEq :=
    localOnly fanPoint fanPointMember
      (pointsEq ▸ tilePointMember)
  rw [← fanPointEq, localEq]
  rw [physicalLaneEq]
  unfold ribbonMacrocellExit
  rw [directionEq]

/-- The final same-colored corridor tile is ordinarily separated from its
coordinated clause fan. -/
theorem finalRibbonMacrocellRoute_avoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (routeLeading : List Cell)
    (previous before target : Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        routeLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (previousUnit : AxisDirection.IsUnitAxisStep previous before)
    (noReverse :
      AxisDirection.between before target ≠
        (AxisDirection.between previous before).opposite) :
    RoutesAvoidEachOther
      (ribbonMacrocellRoute before
        (AxisDirection.between previous before)
        (AxisDirection.between before target)
        (routedRibbonLane source.erase entry color))
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  have targetEq : target = occurrenceSourceClauseTarget planar entry := by
    have endpoint := (occurrenceUnitSourceRoute_endpoints planar entry).2
    rw [routeEquation] at endpoint
    simpa [occurrenceSourceClauseTarget] using endpoint
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry color
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      planar clauseIndex entry entry.mem_activeClauseOccurrenceEntries
  have directionEq :
      data.direction group = AxisDirection.between before target := by
    rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
      planar width entry]
    change AxisDirection.polylineLastDirection
        (occurrenceUnitSourceRoute planar entry) =
      AxisDirection.between before target
    rw [routeEquation,
      AxisDirection.polylineLastDirection_append_pair routeLeading finalUnit]
  have directionGenuine : (data.direction group).IsGenuine := by
    rw [directionEq]
    exact AxisDirection.between_isGenuine_of_unitAxisStep finalUnit
  have beforeStep :
      before = Cell.add target (data.direction group).opposite.step := by
    have forward := AxisDirection.add_between_step_eq_of_unitAxisStep finalUnit
    rw [← directionEq] at forward
    apply Cell.add_left_injective (data.direction group).step
    calc
      Cell.add (data.direction group).step before =
          Cell.add before (data.direction group).step := by
        rcases before with ⟨beforeX, beforeY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        simp [Cell.add, add_comm]
      _ = target := forward.symm
      _ = Cell.add
          (Cell.add target (data.direction group).opposite.step)
          (data.direction group).step :=
        (AxisDirection.add_opposite_step_add_step
          target directionGenuine).symm
      _ = Cell.add (data.direction group).step
          (Cell.add target (data.direction group).opposite.step) := by
        rcases target with ⟨targetX, targetY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        rcases (data.direction group).opposite.step with ⟨oppositeX, oppositeY⟩
        simp [Cell.add, add_comm]
  have localAvoid :=
    data.matchingRibbonMacrocellRoute_avoids_coordinatedRoute
      (compatible.2 entry) group active lane
      (AxisDirection.between previous before)
      (AxisDirection.between_isGenuine_of_unitAxisStep previousUnit)
      directionGenuine (by rw [directionEq]; exact noReverse)
  have translatedAvoid :=
    routesAvoidEachOther_translate localAvoid
      (ribbonMacrocellOrigin target)
  have tileTranslation :
      translatePolyline (ribbonMacrocellOrigin target)
          (ribbonMacrocellRoute (data.direction group).opposite.step
            (AxisDirection.between previous before)
            (data.direction group) lane) =
        ribbonMacrocellRoute before
          (AxisDirection.between previous before)
          (AxisDirection.between before target) lane := by
    unfold translatePolyline
    rw [← ribbonMacrocellRoute_add_center, ← beforeStep,
      directionEq]
  change RoutesAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin target)
        (ribbonMacrocellRoute (data.direction group).opposite.step
          (AxisDirection.between previous before)
          (data.direction group) lane))
      (translatePolyline (ribbonMacrocellOrigin target)
        (data.coordinatedRoute group lane)) at translatedAvoid
  rw [tileTranslation] at translatedAvoid
  simpa [occurrenceCoordinatedRibbonClauseStub, targetEq,
    planar, clauseIndex, data, group, lane] using translatedAvoid

/-- The final corridor boundary is the only listed point shared by the
matching same-colored tile and its coordinated clause fan. -/
theorem finalRibbonMacrocellRoute_occurrenceCoordinatedRibbonClauseStub_only_common
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (routeLeading : List Cell)
    (previous before target : Cell)
    (routeEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        routeLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (previousUnit : AxisDirection.IsUnitAxisStep previous before)
    (noReverse :
      AxisDirection.between before target ≠
        (AxisDirection.between previous before).opposite) :
    ∀ point,
      point ∈ ribbonMacrocellRoute before
        (AxisDirection.between previous before)
        (AxisDirection.between before target)
        (routedRibbonLane source.erase entry color) →
      point ∈ occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry color →
      point = ribbonMacrocellExit before
        (AxisDirection.between before target)
        (routedRibbonLane source.erase entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  have targetEq : target = occurrenceSourceClauseTarget planar entry := by
    have endpoint := (occurrenceUnitSourceRoute_endpoints planar entry).2
    rw [routeEquation] at endpoint
    simpa [occurrenceSourceClauseTarget] using endpoint
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry color
  let origin := ribbonMacrocellOrigin target
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      planar clauseIndex entry entry.mem_activeClauseOccurrenceEntries
  have directionEq :
      data.direction group = AxisDirection.between before target := by
    rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
      planar width entry]
    change AxisDirection.polylineLastDirection
        (occurrenceUnitSourceRoute planar entry) =
      AxisDirection.between before target
    rw [routeEquation,
      AxisDirection.polylineLastDirection_append_pair routeLeading finalUnit]
  have directionGenuine : (data.direction group).IsGenuine := by
    rw [directionEq]
    exact AxisDirection.between_isGenuine_of_unitAxisStep finalUnit
  have beforeStep :
      before = Cell.add target (data.direction group).opposite.step := by
    have forward := AxisDirection.add_between_step_eq_of_unitAxisStep finalUnit
    rw [← directionEq] at forward
    apply Cell.add_left_injective (data.direction group).step
    calc
      Cell.add (data.direction group).step before =
          Cell.add before (data.direction group).step := by
        rcases before with ⟨beforeX, beforeY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        simp [Cell.add, add_comm]
      _ = target := forward.symm
      _ = Cell.add
          (Cell.add target (data.direction group).opposite.step)
          (data.direction group).step :=
        (AxisDirection.add_opposite_step_add_step
          target directionGenuine).symm
      _ = Cell.add (data.direction group).step
          (Cell.add target (data.direction group).opposite.step) := by
        rcases target with ⟨targetX, targetY⟩
        rcases (data.direction group).step with ⟨stepX, stepY⟩
        rcases (data.direction group).opposite.step with ⟨oppositeX, oppositeY⟩
        simp [Cell.add, add_comm]
  have localOnly :=
    data.matchingRibbonMacrocellRoute_coordinatedRoute_only_common
      (compatible.2 entry) group active lane
      (AxisDirection.between previous before)
      (AxisDirection.between_isGenuine_of_unitAxisStep previousUnit)
      directionGenuine (by rw [directionEq]; exact noReverse)
  have tileTranslation :
      translatePolyline origin
          (ribbonMacrocellRoute (data.direction group).opposite.step
            (AxisDirection.between previous before)
            (data.direction group) lane) =
        ribbonMacrocellRoute before
          (AxisDirection.between previous before)
          (AxisDirection.between before target) lane := by
    unfold translatePolyline
    rw [← ribbonMacrocellRoute_add_center, ← beforeStep,
      directionEq]
  intro point tileMember fanMember
  have tileMember' :
      point ∈ translatePolyline origin
        (ribbonMacrocellRoute (data.direction group).opposite.step
          (AxisDirection.between previous before)
          (data.direction group) lane) := by
    rw [tileTranslation]
    exact tileMember
  have fanMember' :
      point ∈ translatePolyline origin (data.coordinatedRoute group lane) := by
    simpa [occurrenceCoordinatedRibbonClauseStub, targetEq,
      planar, clauseIndex, data, group, lane, origin] using fanMember
  rcases List.mem_map.mp tileMember' with
    ⟨tilePoint, tilePointMember, tilePointEq⟩
  rcases List.mem_map.mp fanMember' with
    ⟨fanPoint, fanPointMember, fanPointEq⟩
  have pointsEq : tilePoint = fanPoint :=
    cell_add_left_injective origin
      (tilePointEq.trans fanPointEq.symm)
  have localEq :=
    localOnly tilePoint tilePointMember
      (pointsEq ▸ fanPointMember)
  rw [← tilePointEq, localEq]
  simpa [origin, lane, directionEq, ribbonMacrocellEntry] using
    (ribbonMacrocellExit_eq_entry_of_unitAxisStep
      finalUnit lane).symm

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
